"""Export and validate the three difficulty levels of a security benchmark."""

import argparse
import json
import re
import shutil
import subprocess
import tempfile
from pathlib import Path

from generate_refinement_cases import clean

ROOT = Path(__file__).resolve().parents[1]
THEORY = ROOT / "theories" / "SecurityNoninterference"
THEORIES = {
    "none": THEORY,
    "recursion": ROOT / "theories" / "SecurityNoninterferenceRecursion",
    "if": ROOT / "theories" / "SecurityNoninterferenceIf",
    "if-recursion": ROOT / "theories" / "SecurityNoninterferenceIfRecursion",
}
FILES = ["Syntax", "Semantics", "Typing", "Evaluation", "Metatheory",
         "Substitution", "LogicalRelation", "Noninterference"]
DECL = re.compile(r"^(Definition|Fixpoint|Inductive|Record|Lemma|Theorem|Corollary) (\w+)\b", re.M)
HEADER = '''From Stdlib Require Import Arith.PeanoNat Lists.List Lia.
Import ListNotations.
Reserved Notation "t '-->' t'" (at level 40).
'''
MULTI_NOTATION = 'Notation "t \'-->*\' t\'" := (multi t t\') (at level 40).\n'


def read_declarations(feature="none"):
    declarations = {}
    origins = {}
    for file in FILES:
        text = clean((THEORIES[feature] / f"{file}.v").read_text())
        text = re.sub(r"^(?:From |Import |Reserved Notation |Notation )[^\n]*\n", "", text, flags=re.M)
        matches = list(DECL.finditer(text))
        for i, match in enumerate(matches):
            name = match[2]
            assert name not in declarations, name
            end = matches[i + 1].start() if i + 1 < len(matches) else len(text)
            declarations[name] = "\n".join(
                line for line in text[match.start():end].splitlines() if line.strip()
            ) + "\n"
            origins[name] = (file, match[1])
    return declarations, origins


def dependency_closure(roots, declarations):
    owners = {name: name for name in declarations}
    for name, body in declarations.items():
        if body.startswith(("Inductive ", "Record ")):
            for member in re.findall(r"^\s*(?:\|\s*)?(\w+)\s*:", body, re.M):
                owners[member] = name
    selected = set(roots)
    pending = list(roots)
    while pending:
        name = pending.pop()
        for token in re.findall(r"\b\w+\b", declarations[name]):
            dependency = owners.get(token)
            if dependency is not None and dependency not in selected:
                selected.add(dependency)
                pending.append(dependency)
    return selected


def render(names, declarations, header=True):
    chunks = [HEADER] if header else []
    for name, body in declarations.items():
        if name in names:
            chunks.append(body)
            if name == "multi":
                chunks.append(MULTI_NOTATION)
    return "\n".join(chunks)


def card(difficulty, target, feature="none"):
    slug = f"security-noninterference-{feature}-{difficulty.lower()}"
    configuration = {
        "none": "The feature configuration is the base language.",
        "if": "The feature configuration adds a primitive if-then-else construct. Booleans use the existing sum of two unit types. Only the selected branch is evaluated, and its result is protected by the condition's indirect-reader level.",
        "if-recursion": "The feature configuration combines primitive if-then-else with security-labeled natural numbers, successor, and System T-style natural-number recursion. Booleans use the existing sum of two unit types. Conditional results are protected by the condition's indirect-reader level; recursion results are protected by the count's indirect-reader level.",
        "recursion": "The feature configuration adds security-labeled natural numbers, successor, and System T-style natural-number recursion. The recursion count is evaluated at runtime; each step receives the predecessor and the previous result. The result is protected by the count's indirect-reader level.",
    }[feature]
    supplied = {
        "Hard": "",
        "Medium": "The file additionally supplies the logical relation formed by `value_relation` and `expression_relation`, together with its direct dependencies.\n\n",
        "Easy": "The file additionally supplies the logical relation formed by `value_relation` and `expression_relation`, together with its dependencies, and a proved fundamental theorem `fundamental_expressions`. Only the target theorem remains unproved.\n\n",
    }[difficulty]
    output = {
        "Hard": "construct a logical relation, formulate and prove its fundamental theorem, and prove the target theorem",
        "Medium": "use the supplied logical relation to formulate and prove its fundamental theorem, and prove the target theorem",
        "Easy": "use the supplied proved fundamental theorem to prove the target theorem",
    }[difficulty]
    title = {"if": "If-then-else", "if-recursion": "If-then-else + Recursion"}.get(feature, feature.title())
    return f'''# Security Noninterference — {title} — {difficulty}

## Input

- `benchmarks/{slug}/input/Task.v` — the single self-contained Rocq input file.

The base language is a locally nameless, recursion-free fragment of the SLam calculus with unit, sums, products, functions, security annotations, subtyping, and protection. Evaluation is left-to-right call-by-value, with security levels `Low` and `High`.

{configuration}

{supplied}## Target Theorem

```coq
{target.strip()}
```

Two closed terms of the same secret type are placed in the same typed program context. If the result type is ground and transparent, and the secret's indirect-reader level cannot flow to the result's indirect-reader level, any two completed evaluations produce equal results after security annotations are erased. This is termination-insensitive noninterference.

## Expected Output

Complete `Task.v`: {output}. The completed file must compile with Rocq and must not use `Admitted`, added axioms, unsafe flags, or changes to the supplied language definitions and theorem statements.
'''


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--feature", choices=THEORIES, default="none")
    feature = parser.parse_args().feature
    declarations, origins = read_declarations(feature)
    target = declarations["noninterference"].split("Proof.", 1)[0].strip() + "\n"
    base = {name for name, (file, kind) in origins.items()
            if kind not in {"Lemma", "Theorem", "Corollary"}
            and (file in {"Syntax", "Semantics", "Typing"}
                 or name in {"program_context", "plug", "context_has_type", "ground",
                             "transparent_at", "transparent", "same_result"})}
    base = dependency_closure(base, declarations)
    assert all(origins[name][1] not in {"Lemma", "Theorem", "Corollary"} for name in base)
    stages = {
        "Hard": base,
        "Medium": dependency_closure(base | {"value_relation", "expression_relation"}, declarations),
        "Easy": dependency_closure(base | {"fundamental_expressions"}, declarations),
    }
    assert all(origins[name][1] not in {"Lemma", "Theorem", "Corollary"} for name in stages["Medium"])
    assert "noninterference" not in stages["Easy"]
    assert "ground_related_values_equal" not in stages["Easy"]
    assert "expression_relation_same_result" not in stages["Easy"]
    rocq = shutil.which("rocq")
    if not rocq:
        raise RuntimeError("Rocq is required to validate the exports")
    tasks = {}
    with tempfile.TemporaryDirectory(prefix="noninterference-export-") as temp:
        work = Path(temp)
        for difficulty, selected in stages.items():
            prefix = render(selected, declarations)
            task = prefix + "\n" + target + "Proof.\nAdmitted.\n"
            tasks[difficulty] = task
            skeleton = work / f"{difficulty}Task.v"
            skeleton.write_text(task)
            subprocess.run([rocq, "compile", "-q", skeleton.name], cwd=work, check=True)
            # Complete precisely this input by adding missing reference lemmas
            # before the target, without altering any supplied declarations.
            missing = set(declarations) - selected - {"noninterference"}
            solution = prefix + "\n" + render(missing, declarations, header=False)
            solution += "\n" + declarations["noninterference"] + "\nPrint Assumptions noninterference.\n"
            assert not re.search(r"\b(?:Admitted|Axiom|Parameter)\b", solution)
            path = work / f"{difficulty}Solution.v"
            path.write_text(solution)
            result = subprocess.run([rocq, "compile", "-q", path.name], cwd=work,
                                    text=True, capture_output=True)
            if result.returncode:
                raise RuntimeError(result.stdout + result.stderr)
            if "Closed under the global context" not in result.stdout:
                raise RuntimeError(f"Unexpected assumptions: {result.stdout}")
            subprocess.run([rocq, "check", "-silent", path.stem], cwd=work, check=True)
            print(f"{difficulty}: skeleton and completed proof checked ({len(task.splitlines())} lines)", flush=True)
    bibliography = '''@inproceedings{heintze1998slam,
  author = {Nevin Heintze and Jon G. Riecke},
  title = {The {SLam} Calculus: Programming with Secrecy and Integrity},
  booktitle = {Proceedings of the 25th ACM SIGPLAN-SIGACT Symposium on Principles of Programming Languages},
  year = {1998},
  pages = {365--377},
  doi = {10.1145/268946.268976}
}
'''
    for difficulty, task in tasks.items():
        directory = ROOT / "benchmarks" / f"security-noninterference-{feature}-{difficulty.lower()}"
        (directory / "input").mkdir(parents=True, exist_ok=True)
        for filename in ["Task.v", "Task.v.orig"]:
            (directory / "input" / filename).write_text(task)
        (directory / "card.md").write_text(card(difficulty, target, feature))
        (directory / "references.bib").write_text(bibliography)
        metadata = {"difficulty": difficulty, "public_formalization_exists": None,
                    "references": ["references.bib"], "notes": []}
        (directory / "metadata.json").write_text(json.dumps(metadata, indent=2) + "\n")


if __name__ == "__main__":
    main()
