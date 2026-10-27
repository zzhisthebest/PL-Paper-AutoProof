"""Display-only alpha normalization of quantified Rocq statements.

This is not a Rocq equivalence checker. Unsupported binding syntax is kept
verbatim; proofs, definitions and global identifiers are never renamed.
"""
import re
import textwrap
from dataclasses import dataclass

TOKEN = re.compile(r'\.\(|-->[A-Za-z]+|<\{|\}>|\\[A-Za-z]+|[A-Za-z_][\w\x27]*(?:\.[A-Za-z_][\w\x27]*)*|\d+|[!$%&*+\-./:<=>?@\\^|~]+|[^\s]')
IDENT = re.compile(r'[A-Za-z_][\w\x27]*\Z')
OPEN = {'(': ')', '.(': ')', '[': ']', '{': '}', '<{': '}>'}


class Unsupported(ValueError):
    pass


@dataclass(frozen=True)
class Bound:
    index: int


def normalize_statement(statement):
    """Return display text/status; never silently guess a binder's scope."""
    tokens = TOKEN.findall(statement)
    # These constructs introduce scopes/patterns not handled by this parser.
    if any(t in {'let', 'match', 'fix', 'cofix', 'if', 'lambda', 'as',
                 'return', 'where', ':=', '`', "'", '"', '%', '@', ';', '|'} for t in tokens):
        return dict(status='unsupported', text=None)
    try:
        if len(tokens) < 4 or tokens[0] not in {'Lemma', 'Theorem', 'Corollary', 'Proposition'} or tokens[2] != ':' or tokens[-1] != '.':
            raise Unsupported()
        pairs, stack = {}, []
        for i, token in enumerate(tokens):
            if token in OPEN:
                stack.append(i)
            elif token in OPEN.values():
                if not stack or OPEN[tokens[stack[-1]]] != token:
                    raise Unsupported()
                pairs[stack.pop()] = i
        if stack:
            raise Unsupported()

        count, free = 0, set()

        def fresh(name, env):
            nonlocal count
            if not IDENT.fullmatch(name):
                raise Unsupported()
            count += 1
            bound = Bound(count)
            if name != '_':
                env[name] = bound
            return bound

        def boundary(start, end, delimiter):
            i = start
            while i < end:
                if tokens[i] == delimiter:
                    return i
                if tokens[i] in {'forall', 'exists', 'fun'}:
                    raise Unsupported()
                if tokens[i] in OPEN:
                    i = pairs[i] + 1
                else:
                    i += 1
            raise Unsupported()

        def binders(start, end, env):
            out, i = [], start
            while i < end:
                if tokens[i] in {'(', '{'}:
                    close = pairs[i]
                    if close >= end:
                        raise Unsupported()
                    out += [tokens[i]] + binders(i+1, close, env) + [tokens[close]]
                    i = close + 1
                    continue
                names = []
                while i < end and IDENT.fullmatch(tokens[i]):
                    if tokens[i] in {'forall', 'exists', 'fun'}:
                        raise Unsupported()
                    names.append(tokens[i])
                    i += 1
                if not names:
                    raise Unsupported()
                annotation = None
                if i < end and tokens[i] == ':':
                    # In (x y : T), T is checked before x/y enter scope.
                    annotation = expression(i+1, end, env.copy())
                    i = end
                out += [fresh(name, env) for name in names]
                if annotation is not None:
                    out += [':'] + annotation
            return out

        def expression(start, end, env):
            out, i = [], start
            while i < end:
                token = tokens[i]
                if token in {'forall', 'exists', 'fun'}:
                    delimiter = '=>' if token == 'fun' else ','
                    split = boundary(i+1, end, delimiter)
                    local = env.copy()
                    out += [token] + binders(i+1, split, local) + [delimiter]
                    # A quantified body's scope ends at this expression's delimiter.
                    return out + expression(split+1, end, local)
                if token in OPEN:
                    close = pairs[i]
                    if close >= end:
                        raise Unsupported()
                    if token == '.(':
                        # A record projection names a global field, not a local
                        # binder with the same spelling.
                        if close != i+2 or not IDENT.fullmatch(tokens[i+1]):
                            raise Unsupported()
                        free.add(tokens[i+1])
                        out += [token, tokens[i+1], ')']
                        i = close+1
                        continue
                    # Reject notation binders (rather than treating them as terms).
                    if token in {'[', '{'}:
                        raise Unsupported()
                    out += [token] + expression(i+1, close, env.copy()) + [tokens[close]]
                    i = close + 1
                    continue
                if token in env:
                    out.append(env[token])
                else:
                    out.append(token)
                    if IDENT.fullmatch(token):
                        free.add(token)
                i += 1
            return out

        body = expression(3, len(tokens)-1, {})
        # Avoid capturing a free/global x1, x2, ... in the rendered statement.
        prefix = 'x'
        while any(f'{prefix}{i}' in free for i in range(1, count+1)):
            prefix = '_' + prefix
        rendered = [f'{prefix}{t.index}' if isinstance(t, Bound) else t for t in body]
        header = ' '.join(tokens[:3])
        text = '\n'.join(textwrap.wrap(header+' '+' '.join(rendered)+' .', width=88,
                                        break_long_words=False, break_on_hyphens=False,
                                        subsequent_indent='  '))
        return dict(status='normalized', text=text)
    except Unsupported:
        return dict(status='unsupported', text=None)
