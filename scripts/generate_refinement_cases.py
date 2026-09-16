"""Export verified refinement theories without leaking later difficulty stages.

Only explicitly selected, verified feature configurations are supported. Validation
uses a fresh directory; repository inputs are replaced only after it succeeds.
"""

from __future__ import annotations

import argparse
import re
import shutil
import subprocess
import tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
SOURCES = {
    "none": "SystemFRefinement", "if": "SystemFRefinementIf",
    "recursion": "SystemFRefinementRecursion",
    "nondeterminism": "SystemFRefinementNonDeterminism",
    "if-nondeterminism": "SystemFRefinementIfNonDeterminism",
    "if-recursion": "SystemFRefinementIfRecursion",
    "nondeterminism-recursion": "SystemFRefinementNonDeterminismRecursion",
    "if-nondeterminism-recursion": "SystemFRefinementIfNonDeterminismRecursion",
}
TARGET = r"""Theorem never_stuck : forall (t t' : tm) (R : rty),
  has_rtype [] empty_rcontext t R ->
  multi t t' ->
  value t' \/ exists t'' : tm, t' --> t''.
"""
DECL = re.compile(r"^(?:Definition|Fixpoint|Inductive|Record|Lemma|Theorem|Corollary|Equations) (\w+)\b", re.M)


def clean(text: str) -> str:
    # Rocq comments nest. Preserve token separation, not empty comment lines.
    out, i, depth, quoted = [], 0, 0, False
    while i < len(text):
        if not quoted and text.startswith("(*", i):
            depth += 1
            out.append(" ")
            i += 2
        elif depth and text.startswith("*)", i):
            depth -= 1
            i += 2
        elif depth:
            if text[i] == "\n":
                out.append("\n")
            i += 1
        else:
            if text[i] == '"':
                quoted = not quoted
            out.append(text[i])
            i += 1
    if depth:
        raise ValueError("Unclosed Rocq comment")
    text = "".join(out)
    text = re.sub(r"^From AutoProof\.[\s\S]*?\.\s*\n", "", text, flags=re.M)
    text = re.sub(r"^Print Assumptions[^\n]*\n?", "", text, flags=re.M)
    text = re.sub(r"[ \t]+\n", "\n", text)
    return re.sub(r"\n{3,}", "\n\n", text).strip() + "\n"


def source(directory: str, name: str) -> str:
    return clean((ROOT / "theories" / directory / (name + ".v")).read_text())


def module_name(text: str) -> str:
    return re.search(r"^Module (\w+)\.", text, re.M)[1]


def through(text: str, name: str, proof: bool = False) -> str:
    start = next(m.start() for m in DECL.finditer(text) if m[1] == name)
    end = text.index("Qed.", start) + 4 if proof else text.index(".\n", start) + 1
    return text[:end] + "\n\nEnd " + module_name(text) + ".\n"


def declarations(text: str, names: list[str]) -> str:
    result = []
    matches = list(DECL.finditer(text))
    for name in names:
        i = next(i for i, m in enumerate(matches) if m[1] == name)
        end = matches[i + 1].start() if i + 1 < len(matches) else text.index("\nEnd ", matches[i].start())
        result.append(text[matches[i].start():end].strip())
    return "\n\n".join(result) + "\n"


def definitions_only(text: str) -> str:
    return re.sub(r"^(?:Lemma|Theorem|Corollary) [\s\S]*?^Qed\.\n", "", text, flags=re.M)


def wrapper(name: str, imports: list[str], body: str) -> str:
    return f"Module {name}.\nImport ListNotations {' '.join(imports)}.\n\n{body}\nEnd {name}.\n"


def export(feature: str, difficulty: str) -> str:
    directory = SOURCES[feature]
    src = {name: source(directory, name) for name in
           ["Syntax", "Infrastructure", "CoreTyping", "RefinementLogic", "RefinementTyping",
            "Evaluation", "Denotations", "RefinementSoundness"]}
    names = {name: module_name(text) for name, text in src.items()}
    if difficulty == "easy":
        pieces = [src[name] for name in ["Syntax", "Infrastructure", "CoreTyping", "RefinementLogic",
                                        "RefinementTyping", "Evaluation", "Denotations"]]
        if "recursion" in feature:
            pieces.append(through(source(directory, "Termination"), "integer_decreases_wf", True))
        pieces.append(through(src["RefinementSoundness"], "fundamental", True))
        imports = list(names.values())
    else:
        pieces = [definitions_only(src["Syntax"])]
        imports = [names["Syntax"]]
        if "recursion" in feature:
            body = declarations(src["Infrastructure"],
                                ["type_substitution", "term_substitution", "instantiate_ty", "instantiate"])
            pieces.append(wrapper(names["Infrastructure"], imports, body))
            imports.append(names["Infrastructure"])
        pieces.append(definitions_only(src["RefinementLogic"]))
        imports.append(names["RefinementLogic"])
        typing = src["RefinementTyping"]
        first_lemma = re.search(r"^Lemma ", typing, re.M).start()
        pieces.append(typing[:first_lemma] + f"End {names['RefinementTyping']}.\n")
        imports.append(names["RefinementTyping"])
        evaluation = declarations(src["Evaluation"], ["multi"])
        if difficulty == "medium":
            evaluation += declarations(src["Evaluation"],
                                       ["must_terminate" if "nondeterminism" in feature else "halts"])
        pieces.append(wrapper(names["Evaluation"], imports, evaluation))
        imports.append(names["Evaluation"])
        if difficulty == "medium":
            body = declarations(src["Denotations"], ["rty_size", "rty_size_open_tm_rec", "rty_size_open_tm",
                                                     "rty_size_open_ty_rec", "rty_size_open_ty", "denotes", "evals_denotes"])
            pieces.append("From Stdlib Require Import Program.Wf.\nFrom Equations Require Import Equations.\n" +
                          wrapper(names["Denotations"], imports, body))
            imports.append(names["Denotations"])
    pieces.append(wrapper(directory + "Task", imports, TARGET + "Proof.\n\nQed.\n"))
    text = clean("\n".join(pieces))
    check_stage(text, difficulty)
    return text


def check_stage(text: str, difficulty: str) -> None:
    names = {m[1] for m in DECL.finditer(text)}
    if re.search(r"\b(?:Admitted|Axiom|Axioms|Parameter|Parameters)\b", text):
        raise ValueError("Unexpected assumption in task input")
    if text.count(TARGET) != 1 or text.count("Proof.\n\nQed.") != 1:
        raise ValueError("Expected exactly one unfinished target theorem")
    proofs = set(re.findall(r"^(?:Lemma|Theorem|Corollary) (\w+)", text, re.M))
    if difficulty == "hard":
        assert not {"denotes", "evals_denotes", "fundamental"} & names
        assert proofs == {"never_stuck"}, proofs
    elif difficulty == "medium":
        assert {"denotes", "evals_denotes"} <= names and "fundamental" not in names
        assert proofs == {"never_stuck", "rty_size_open_tm_rec", "rty_size_open_tm",
                          "rty_size_open_ty_rec", "rty_size_open_ty"}, proofs
    else:
        assert {"denotes", "evals_denotes", "fundamental"} <= names
        assert not {"denotational_soundness", "refinement_termination", "subtyping_sound"} & names


def card(feature: str, difficulty: str) -> str:
    name = f"systemf-refinement-soundness-{feature}-{difficulty}"
    descriptions = {
        "if": "The if-then-else feature adds Booleans and a Boolean conditional.",
        "nondeterminism": "Binary choice may reduce to either operand; safety covers every branch.",
        "recursion": "Recursive functions are checked by a nonnegative, strictly decreasing integer metric, with an integer zero test for branching.",
    }
    extra = " ".join(descriptions[f] for f in feature.split("-") if f in descriptions)
    if feature == "none":
        extra = "The feature configuration is the base language."
    if "recursion" in feature and "nondeterminism" in feature:
        extra += " Strict metric comparisons must hold for all possible integer outcomes."
    supplied = {"hard": "", "medium": " It supplies the logical relation: `denotes R v` interprets refinement types at values, "
                "and `evals_denotes R t` requires termination and constrains every reachable value.",
                "easy": " It supplies the logical relation (`denotes` and `evals_denotes`) and a proved fundamental theorem "
                f"`{SOURCES[feature]}Soundness.fundamental`."}[difficulty]
    work = {"hard": "construct a logical relation and its context interpretation, prove a fundamental theorem, then prove the target theorem",
            "medium": "use the supplied logical relation, define its context interpretation, prove a fundamental theorem, then prove the target theorem",
            "easy": "use the supplied logical relation and proved fundamental theorem to prove the target theorem"}[difficulty]
    return f"""# System F Refinement Type Safety — {feature.capitalize()} — {difficulty.capitalize()}

## Input

- `benchmarks/{name}/input/Task.v` — the single self-contained Rocq input file.

The language is locally nameless System F with integers, addition, subtraction, multiplication, and partial division. Its refinement layer uses Boolean formulas, refinement function, existential, and polymorphic types, subtyping, and refinement typing. Division requires a nonzero divisor. {extra}

The file supplies the language syntax, call-by-value small-step semantics, core and refinement typing rules, and the target theorem.{supplied}

## Target Theorem

```coq
{TARGET.rstrip()}
```

Every state reachable from a closed refinement-typed program is a value or can take another step.

## Expected Output

Complete `Task.v`: {work}. The completed file must compile with Rocq and must not use `Admitted`, added axioms, unsafe flags, or changes to the supplied language definitions and theorem statements.
"""


def patch_file(path: Path, text: str) -> None:
    if path.exists():
        old = path.read_text()
        if old == text:
            return
        patch = f"*** Update File: {path}\n@@\n" + "".join("-" + line + "\n" for line in old.splitlines())
        patch += "".join("+" + line + "\n" for line in text.splitlines())
    else:
        patch = f"*** Add File: {path}\n" + "".join("+" + line + "\n" for line in text.splitlines())
    subprocess.run(["apply_patch"], input="*** Begin Patch\n" + patch + "*** End Patch\n", text=True, check=True, stdout=subprocess.DEVNULL)


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("features", nargs="+", choices=SOURCES)
    parser.add_argument("--write", action="store_true", help="Update validated repository inputs and cards")
    parser.add_argument("--rocq", default=shutil.which("rocq"))
    args = parser.parse_args()
    if not args.rocq:
        parser.error("Rocq executable not found")
    work = Path(tempfile.mkdtemp(prefix="refinement-case-check."))
    print(f"Validation directory: {work}", flush=True)
    pending = []
    for feature in args.features:
        directory = SOURCES[feature]
        modules = ["Syntax", "Infrastructure", "CoreTyping", "RefinementLogic", "RefinementTyping", "Evaluation", "Denotations"]
        if "recursion" in feature:
            modules.append("Termination")
        full = "\n".join(source(directory, m) for m in modules + ["RefinementSoundness", "Safety"])
        reference = work / (feature.replace("-", "_") + "_reference.v")
        patch_file(reference, full)
        subprocess.run([args.rocq, "compile", "-q", reference.name], cwd=work, check=True)
        subprocess.run([args.rocq, "check", "-silent", reference.stem], cwd=work, check=True)
        for difficulty in ("hard", "medium", "easy"):
            text = export(feature, difficulty)
            path = work / f"{feature.replace('-', '_')}_{difficulty}.v"
            # Only the unfinished target is admitted in this disposable prefix check.
            patch_file(path, text.replace(TARGET + "Proof.\n\nQed.", TARGET + "Admitted."))
            subprocess.run([args.rocq, "compile", "-q", path.name], cwd=work, check=True)
            case = ROOT / "benchmarks" / f"systemf-refinement-soundness-{feature}-{difficulty}"
            task, orig = case / "input/Task.v", case / "input/Task.v.orig"
            if task.read_bytes() != orig.read_bytes():
                raise RuntimeError(f"Preserving user-modified task: {task}")
            pending.extend([(task, text), (orig, text), (case / "card.md", card(feature, difficulty))])
            print(f"Checked {feature}/{difficulty}", flush=True)
    if args.write:
        for path, text in pending:
            patch_file(path, text)
        print(f"Updated {len(pending) // 3} cases.", flush=True)


if __name__ == "__main__":
    main()
