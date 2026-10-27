"""Interpret recorded text edits in memory. Never run trace commands or Python.

Unsupported syntax invalidates the virtual files; subsequent literal writes or
recorded full snapshots can re-establish them. This is not a shell emulator.
"""
import ast
import fnmatch
import posixpath
import re
import shlex


class Unknown(Exception):
    pass


class LoopBreak(Exception):
    pass


class LoopContinue(Exception):
    pass


class ScriptExit(Exception):
    pass


class FunctionReturn(Exception):
    def __init__(self, value):
        self.value = value


class TextPython:
    """Small AST interpreter for the string/list editing scripts in the traces."""
    def __init__(self, files, cwd, argv=None):
        self.files, self.cwd, self.names = files, cwd, {}
        self.functions = {}
        self.argv = argv or ['-']
        self.global_scope = None
        self.global_names = set()
        self.call_depth = 0

    def expr(self, n):
        if isinstance(n, ast.Constant):
            return n.value
        if isinstance(n, ast.Name):
            if n.id == 're':
                return ('regex-module',)
            return self.names[n.id]
        if isinstance(n, ast.Tuple):
            return tuple(self.expr(x) for x in n.elts)
        if isinstance(n, ast.List):
            return [self.expr(x) for x in n.elts]
        if isinstance(n, ast.Dict) and all(k is not None for k in n.keys):
            return {self.expr(k): self.expr(v) for k, v in zip(n.keys, n.values)}
        if isinstance(n, (ast.ListComp, ast.GeneratorExp)) and len(n.generators) == 1 and not n.generators[0].is_async:
            gen = n.generators[0]
            values = self.expr(gen.iter)
            if not isinstance(values, (list, tuple)) or len(values) > 10000:
                raise Unknown('comprehension iterable')
            saved = self.names
            self.names = dict(saved)
            try:
                result = []
                for value in values:
                    self.assign(gen.target, value)
                    if all(self.expr(cond) for cond in gen.ifs):
                        result.append(self.expr(n.elt))
                return iter(result) if isinstance(n, ast.GeneratorExp) else result
            finally:
                self.names = saved
        if isinstance(n, ast.JoinedStr):
            return ''.join(str(self.expr(x)) for x in n.values)
        if isinstance(n, ast.FormattedValue) and n.format_spec is None:
            value = self.expr(n.value)
            return repr(value) if n.conversion == 114 else str(value)
        if isinstance(n, ast.IfExp):
            return self.expr(n.body if self.expr(n.test) else n.orelse)
        if isinstance(n, ast.Attribute) and isinstance(n.value, ast.Name) and n.value.id == 're':
            if n.attr in ('S', 'M', 'I', 'DOTALL', 'MULTILINE', 'IGNORECASE'):
                return getattr(re, n.attr)
        if isinstance(n, ast.Attribute) and isinstance(n.value, ast.Name) and n.value.id == 'sys' and n.attr == 'argv':
            return self.argv
        if isinstance(n, ast.Slice):
            return slice(*(self.expr(x) if x else None for x in (n.lower, n.upper, n.step)))
        if isinstance(n, ast.Subscript):
            return self.expr(n.value)[self.expr(n.slice)]
        if isinstance(n, ast.BinOp):
            a, b = self.expr(n.left), self.expr(n.right)
            if isinstance(n.op, ast.Add):
                return a + b
            if isinstance(n.op, ast.Sub):
                return a - b
            if isinstance(n.op, ast.Mod):
                return a % b
        if isinstance(n, ast.UnaryOp) and isinstance(n.op, ast.USub):
            return -self.expr(n.operand)
        if isinstance(n, ast.UnaryOp) and isinstance(n.op, ast.Not):
            return not self.expr(n.operand)
        if isinstance(n, ast.BoolOp):
            value = self.expr(n.values[0])
            for item in n.values[1:]:
                if isinstance(n.op, ast.And) and not value or isinstance(n.op, ast.Or) and value:
                    break
                value = self.expr(item)
            return value
        if isinstance(n, ast.Compare) and len(n.ops) == 1:
            a, b = self.expr(n.left), self.expr(n.comparators[0])
            if isinstance(n.ops[0], ast.In):
                return a in b
            if isinstance(n.ops[0], ast.Eq):
                return a == b
            if isinstance(n.ops[0], ast.NotIn):
                return a not in b
            if isinstance(n.ops[0], ast.NotEq):
                return a != b
            if isinstance(n.ops[0], ast.Is):
                return a is b
            if isinstance(n.ops[0], ast.IsNot):
                return a is not b
            if isinstance(n.ops[0], ast.Lt):
                return a < b
            if isinstance(n.ops[0], ast.LtE):
                return a <= b
            if isinstance(n.ops[0], ast.Gt):
                return a > b
            if isinstance(n.ops[0], ast.GtE):
                return a >= b
        if isinstance(n, ast.Call):
            args = [self.expr(x) for x in n.args]
            kw = {x.arg: self.expr(x.value) for x in n.keywords}
            if isinstance(n.func, ast.Name):
                if n.func.id in self.functions:
                    fn = self.functions[n.func.id]
                    if kw or len(args) != len(fn.args.args):
                        raise Unknown('function arguments')
                    saved = self.names
                    old_scope, old_globals = self.global_scope, self.global_names
                    if self.call_depth >= 20:
                        raise Unknown('function recursion limit')
                    self.global_scope = old_scope if old_scope is not None else saved
                    self.global_names = set()
                    self.names = dict(saved, **{p.arg: v for p, v in zip(fn.args.args, args)})
                    self.call_depth += 1
                    try:
                        self.statements(fn.body)
                    except FunctionReturn as result:
                        return result.value
                    finally:
                        self.call_depth -= 1
                        self.names = saved
                        self.global_scope, self.global_names = old_scope, old_globals
                    return None
                if n.func.id == 'open':
                    path = resolve_path(args[0], self.cwd)
                    return ('file', path, args[1] if len(args) > 1 else 'r')
                if n.func.id == 'len':
                    return len(*args)
                if n.func.id == 'str':
                    return str(*args)
                if n.func.id == 'repr':
                    return repr(*args)
                if n.func.id == 'zip':
                    return list(zip(*args))
                if n.func.id in ('min', 'max', 'all', 'any', 'next'):
                    return {'min': min, 'max': max, 'all': all, 'any': any, 'next': next}[n.func.id](*args)
                if n.func.id == 'enumerate':
                    return list(enumerate(*args))
                if n.func.id == 'range':
                    result = range(*args)
                    if len(result) > 10000:
                        raise Unknown('range too large')
                    return list(result)
                if n.func.id == 'print':
                    return None
            if isinstance(n.func, ast.Attribute):
                obj, method = self.expr(n.func.value), n.func.attr
                if obj == ('regex-module',) and method == 'finditer':
                    return list(re.finditer(*args, **kw))
                if obj == ('regex-module',) and method in {'sub', 'subn', 'compile', 'escape', 'findall', 'search', 'match'}:
                    return getattr(re, method)(*args, **kw)
                if isinstance(obj, re.Pattern) and method in {'sub', 'subn', 'findall', 'search', 'match'}:
                    return getattr(obj, method)(*args, **kw)
                if isinstance(obj, re.Match) and method in {'group', 'start', 'end'}:
                    return getattr(obj, method)(*args, **kw)
                if isinstance(obj, tuple) and obj[0] == 'file':
                    _, path, mode = obj
                    if method in ('read', 'readlines') and mode == 'r':
                        text = self.files[path]
                        return text if method == 'read' else text.splitlines(True)
                    if method in ('write', 'writelines') and mode in ('w', 'a'):
                        text = args[0] if method == 'write' else ''.join(args[0])
                        self.files[path] = (self.files[path] if mode == 'a' else '') + text
                        return len(text)
                allowed = {'replace', 'split', 'splitlines', 'join', 'index', 'rindex', 'find',
                           'rfind', 'strip', 'rstrip', 'lstrip', 'startswith', 'endswith', 'count'}
                if isinstance(obj, str) and method in allowed:
                    return getattr(obj, method)(*args, **kw)
                if isinstance(obj, list) and method in {'append', 'extend', 'insert', 'pop', 'index', 'count'}:
                    return getattr(obj, method)(*args, **kw)
                if isinstance(obj, dict) and method in {'items', 'keys', 'values'}:
                    return list(getattr(obj, method)(*args, **kw))
        raise Unknown(type(n).__name__)

    def assign(self, node, value):
        if isinstance(node, ast.Name):
            self.names[node.id] = value
            if node.id in self.global_names and self.global_scope is not None:
                self.global_scope[node.id] = value
        elif isinstance(node, ast.Subscript):
            self.expr(node.value)[self.expr(node.slice)] = value
        elif isinstance(node, (ast.Tuple, ast.List)):
            if len(node.elts) != len(value):
                raise Unknown('unpacking length')
            for target, item in zip(node.elts, value):
                self.assign(target, item)
        else:
            raise Unknown('assignment')

    def run(self, source):
        self.statements(ast.parse(source).body)

    def statements(self, nodes):
        for n in nodes:
            if isinstance(n, (ast.Import, ast.ImportFrom)):
                continue  # imports are NOT performed
            if isinstance(n, ast.Assign):
                v = self.expr(n.value)
                for target in n.targets:
                    self.assign(target, v)
            elif isinstance(n, ast.AugAssign) and isinstance(n.op, ast.Add):
                self.assign(n.target, self.expr(n.target) + self.expr(n.value))
            elif isinstance(n, ast.Expr):
                self.expr(n.value)
            elif isinstance(n, ast.Return):
                raise FunctionReturn(self.expr(n.value) if n.value else None)
            elif isinstance(n, ast.Global):
                self.global_names.update(n.names)
            elif isinstance(n, ast.Delete):
                for target in n.targets:
                    if not isinstance(target, ast.Subscript):
                        raise Unknown('delete target')
                    del self.expr(target.value)[self.expr(target.slice)]
            elif isinstance(n, ast.Assert):
                if not self.expr(n.test):
                    raise AssertionError('assertion failed')
            elif (isinstance(n, ast.Raise) and isinstance(n.exc, ast.Call)
                  and isinstance(n.exc.func, ast.Name) and n.exc.func.id == 'SystemExit'):
                raise ScriptExit('SystemExit')
            elif isinstance(n, ast.For):
                values = self.expr(n.iter)
                if not isinstance(values, (list, tuple)) or len(values) > 10000:
                    raise Unknown('unsupported loop iterable')
                for value in values:
                    self.assign(n.target, value)
                    try:
                        self.statements(n.body)
                    except LoopContinue:
                        continue
                    except LoopBreak:
                        break
                else:
                    self.statements(n.orelse)
            elif isinstance(n, ast.Pass):
                continue
            elif isinstance(n, ast.Break):
                raise LoopBreak()
            elif isinstance(n, ast.Continue):
                raise LoopContinue()
            elif isinstance(n, ast.If):
                self.statements(n.body if self.expr(n.test) else n.orelse)
            elif isinstance(n, ast.With):
                for item in n.items:
                    value = self.expr(item.context_expr)
                    if not isinstance(value, tuple) or value[0] != 'file':
                        raise Unknown('unsupported context manager')
                    if item.optional_vars:
                        self.assign(item.optional_vars, value)
                self.statements(n.body)
            elif isinstance(n, ast.FunctionDef) and not n.decorator_list and not n.args.defaults and not n.args.vararg and not n.args.kwarg:
                self.functions[n.name] = n
            else:
                raise Unknown(type(n).__name__)


def chunks(command):
    """Separate heredoc bodies before tokenizing shell operators."""
    lines = command.splitlines(True)
    i = 0
    while i < len(lines):
        head = lines[i]
        i += 1
        m = re.search(r"<<(-?)\s*(['\"]?)([A-Za-z_][\w]*)(\2)", head)
        body = None
        if m:
            body = ''
            while i < len(lines):
                line = lines[i]
                i += 1
                if (line.lstrip('\t') if m[1] else line).rstrip('\r\n') == m[3]:
                    break
                body += line.lstrip('\t') if m[1] else line
            # Bash accepts end-of-input as a heredoc terminator with a warning;
            # all remaining text is still written, including accidental prose.
            if not m[2] and re.search(r'[$`\\]', body):
                body = None  # shell expansion would change this body
            head = head[:m.start()] + '__HEREDOC__' + head[m.end():]
        while True:
            lexer = shlex.shlex(head, posix=True, punctuation_chars=';&|<>')
            lexer.whitespace_split = True
            try:
                words = list(lexer)
                break
            except ValueError as error:
                if 'No closing quotation' not in str(error) or i >= len(lines):
                    raise
                head += lines[i]
                i += 1
        # Pipes/redirections are kept with their command; never confuse quoted
        # Rocq semicolons with shell separators after tokenization.
        part = []
        for word in words:
            if word in ('&&', ';', '||'):
                if part:
                    yield part, body if '__HEREDOC__' in part else None, word
                part = []
            else:
                part.append(word)
        if part:
            yield part, body if '__HEREDOC__' in part else None, '\n'


READ_ONLY = {'coqc', 'rocqc', 'rocq', 'coqtop', 'grep', 'rg', 'wc', 'ls', 'pwd', 'diff',
             'find', 'echo', 'printf', 'head', 'tail', 'cat', 'sed', 'awk', 'true',
             'mkdir', 'sleep', 'timeout', 'env', 'date', 'nl', 'which', 'command',
             'du', 'stat', 'file', 'sort', 'uniq', 'cut', 'chmod', 'false',
             'md5sum', 'sha256sum', 'ps', 'coqchk', 'strings', 'pkill', 'kill'}


def source_read_only(words):
    """Recognize inspection pipelines, not arbitrary commands containing them."""
    if any('$(' in w or '`' in w for w in words):
        if (words[:2] == ['sed', '-n'] and len(words) == 4
                and re.fullmatch(r"\$\(grep -n '[^'\n]+' [\w./-]+ \| cut -d: -f1\),\+\d+p", words[2])):
            return True
        return False
    parts, part = [], []
    i = 0
    while i < len(words):
        w = words[i]
        if w in ('>', '>>'):
            if i + 1 >= len(words):
                return False
            target = words[i + 1]
            if target == '&' and i + 2 < len(words) and words[i + 2].isdigit():
                i += 3
                continue
            if target != '/dev/null':
                return False
            i += 2
            continue
        if w == '|':
            parts.append(part)
            part = []
        else:
            part.append(w)
        i += 1
    parts.append(part)
    for part in parts:
        if not part or part[0] not in READ_ONLY - {'env', 'timeout', 'find'}:
            return False
        if part[0] == 'sed' and any(w.startswith('-i') for w in part[1:]):
            return False
        # sed/awk programs can themselves write files or run commands.
        if part[0] == 'sed' and not ('-n' in part and any(re.fullmatch(r'[\d,$]+p', w) for w in part)):
            return False
        if part[0] == 'awk':
            if len(part) < 2 or not re.fullmatch(
                    r'NR\s*>=?\s*\d+\s*&&\s*NR\s*<=?\s*\d+\s*\{\s*(?:printf\s*"[^"\n]*",\s*NR,\s*\$0|print\s+NR\s*"[^"\n]*"\s*\$0)\s*\}', part[1]):
                return False
    return True


def inspection_loop(command):
    """Recognize name-occurrence reports; these inspect code, never edit it."""
    match = re.fullmatch(r'\s*for\s+(\w+)\s+in\s+[\w\s]+;\s*do\s+(.*?);\s*done(?:\s*[;|]\s*(.*))?\s*', command, re.S)
    if not match:
        return False
    body = match[2]
    # Only permit command substitutions that are themselves read-only pipelines.
    substitutions = re.findall(r'\$\(([^()]*)\)', body)
    for sub in substitutions:
        try:
            if not all(source_read_only(w) for w, _, _ in chunks(sub)):
                return False
        except (ValueError, Unknown):
            return False
    body = re.sub(r'\$\([^()]*\)', '0', body)
    if '$(' in body or '`' in body:
        return False
    try:
        for words, _, _ in chunks(body):
            if words and re.fullmatch(r'\w+=0', words[0]) and len(words) == 1:
                continue
            if words and words[0] == 'if' and words[1:2] == ['['] and words[-1:] == [']']:
                if not any(w in words for w in ('>', '>>', '|')):
                    continue
            if words[:1] == ['then']:
                words = words[1:]
            if words == ['fi']:
                continue
            if not source_read_only(words):
                return False
        return not match[3] or all(source_read_only(w) for w, _, _ in chunks(match[3]))
    except (ValueError, Unknown):
        return False


def write_targets(words, body, cwd, files):
    """Bound the damage of unsupported edits; None means arbitrary effects."""
    def path(w):
        return resolve_path(w, cwd)
    name = words[0]
    try:
        if re.match(r'^\w+=\$\(', name):
            expression = ' '.join(words).split('=', 1)[1]
            if expression.startswith('$(') and expression.endswith(')'):
                inner = expression[2:-1]
                if all(source_read_only(w) for w, _, _ in chunks(inner)):
                    return set()  # An unresolved shell variable is not a file edit.
        if '|' in words and 'tee' in words:
            # Compiler output written to log files does not mutate input code.
            parts, part = [], []
            for w in words + ['|']:
                if w == '|':
                    parts.append(part); part = []
                else:
                    part.append(w)
            targets = set()
            for part in parts:
                if part and part[0] == 'tee':
                    targets.update(path(w) for w in part[1:] if not w.startswith('-'))
                elif not source_read_only(part):
                    return None
            return targets
        if name in ('python', 'python3'):
            source = (body if '__HEREDOC__' in words else
                      words[words.index('-c') + 1] if '-c' in words else files[path(words[1])])
            tree = ast.parse(source)
            # Only inspect text-editing programs. Never assume arbitrary Python
            # (os.system, imported helpers, etc.) has limited filesystem effects.
            allowed = {'open', 'len', 'print', 'str', 'range', 'enumerate',
                       'read', 'readlines', 'write', 'writelines', 'replace', 'split',
                       'splitlines', 'join', 'index', 'find', 'rfind', 'strip', 'rstrip',
                       'lstrip', 'startswith', 'endswith', 'append', 'extend', 'insert',
                       'pop', 'sub', 'search', 'match', 'findall', 'escape', 'count',
                       'next', 'all', 'any', 'sorted', 'set', 'list', 'int', 'dict',
                       'loads', 'get', 'keys', 'values', 'items', 'group', 'start', 'end', 'isinstance',
                       'unified_diff', 'SystemExit', 'compile', 'subn'}
            for n in ast.walk(tree):
                if isinstance(n, ast.Call):
                    label = n.func.id if isinstance(n.func, ast.Name) else n.func.attr if isinstance(n.func, ast.Attribute) else ''
                    if label not in allowed:
                        return None
            names = {}
            assigned = set()
            for n in ast.walk(tree):
                if isinstance(n, ast.Assign):
                    try:
                        value = ast.literal_eval(n.value)
                    except (ValueError, TypeError):
                        value = None
                    for target in n.targets:
                        if isinstance(target, ast.Name):
                            if target.id in assigned:
                                names[target.id] = None
                            else:
                                names[target.id] = value
                            assigned.add(target.id)
            targets = {path(words[i+1]) for i, w in enumerate(words[:-1]) if w in ('>', '>>') and words[i+1] != '&'}
            for n in ast.walk(tree):
                if not (isinstance(n, ast.Call) and isinstance(n.func, ast.Name) and n.func.id == 'open'):
                    continue
                mode_node = n.args[1] if len(n.args) > 1 else next((k.value for k in n.keywords if k.arg == 'mode'), ast.Constant('r'))
                mode = ast.literal_eval(mode_node)
                if not any(flag in mode for flag in 'wax+'):
                    continue
                arg = n.args[0]
                target = names[arg.id] if isinstance(arg, ast.Name) else ast.literal_eval(arg)
                targets.add(path(target))
            return targets
        if name in ('cp', 'mv'):
            operands = [w for w in words[1:] if not w.startswith('-')]
            if len(operands) == 2:
                src, dst = map(path, operands)
                if not posixpath.splitext(dst)[1]:
                    dst = posixpath.join(dst, posixpath.basename(src))
                return {src, dst} if name == 'mv' else {dst}
        if name == 'sed' and any(w.startswith('-i') for w in words[1:]):
            return {path(words[-1])}
        if name in ('cat', 'head', 'tail', 'sed', 'awk', 'printf', 'echo', 'coqc', 'coqtop', 'rocq', 'grep', 'rg', 'git'):
            targets = set()
            for i, w in enumerate(words[:-1]):
                if w in ('>', '>>') and words[i + 1] != '&':
                    targets.add(path(words[i + 1]))
            if targets and not any(('$(' in w and not re.fullmatch(r'\$\(\(\w+\s*[+-]\s*\d+\)\)', w)) or '`' in w for w in words):
                return targets
    except (ValueError, TypeError, KeyError, IndexError, SyntaxError, Unknown):
        pass
    return None


def resolve_path(word, cwd):
    if any(c in word for c in '$`~*?'):
        raise Unknown('dynamic path')
    if posixpath.isabs(word):
        return posixpath.normpath(word)
    if cwd is None:
        raise Unknown('unknown working directory')
    return posixpath.normpath(posixpath.join(cwd, word))


def command_contexts(command, cwd='/workspace'):
    """Keep each command's own cwd; a later cd cannot rewrite earlier paths."""
    result = []
    parts = list(chunks(command))
    # Literal concatenation groups: (echo ...; cat file) > combined.v.
    grouped, in_group = [], False
    for words, body, connector in parts:
        if words and words[0] in ('(echo', '(cat', '(head', '(sed', '(printf'):
            words = ['{', words[0][1:]] + words[1:]
            in_group = True
        if in_group and '>' in words:
            at = words.index('>')
            if at and words[at-1].endswith(')'):
                prefix = words[:at-1] + ([words[at-1][:-1]] if words[at-1] != ')' else [])
                if prefix:
                    grouped.append((prefix, body, ';'))
                grouped.append((['}'] + words[at:], None, connector))
                in_group = False
                continue
        grouped.append((words, body, connector))
    parts = grouped
    flattened, i = [], 0
    while i < len(parts):
        words, body, connector = parts[i]
        if len(words) >= 4 and words[0] == 'for' and words[2] == 'in':
            variable, values = words[1], words[3:]
            if (len(values) == 3 and values[0] == '$(seq' and values[1].isdigit()
                    and re.fullmatch(r'\d+\)', values[2])):
                start, end = int(values[1]), int(values[2][:-1])
                if 0 <= end - start <= 10000:
                    values = [str(n) for n in range(start, end + 1)]
            j = i + 1
            while j < len(parts) and parts[j][0][:1] != ['done']:
                j += 1
            if (j < len(parts) and all(re.fullmatch(r'[\w.-]+', v) for v in values)
                    and not any(re.search(r'\$' + re.escape(variable) + r'\b', q)
                                for q in re.findall(r"'[^']*'", command))):
                group = parts[i+1:j]
                if group and group[0][0][:1] == ['do']:
                    group = [(group[0][0][1:], group[0][1], group[0][2])] + group[1:]
                if group and all(w and (b is None or '$' not in b and '`' not in b)
                                 and w[0] not in ('for', 'if', 'while') for w, b, _ in group):
                    pattern = r'\$\{' + re.escape(variable) + r'\}|\$' + re.escape(variable) + r'\b'
                    closing = parts[j][0]
                    redirected = len(closing) == 3 and closing[1] == '>'
                    if len(closing) != 1 and not (redirected and all(w[0] in ('echo', 'printf') for w, _, _ in group)):
                        flattened.append(parts[i]); i += 1
                        continue
                    emitted = 0
                    for value in values:
                        for w, b, conn in group:
                            expanded = [re.sub(pattern, lambda _: value, word) for word in w]
                            if redirected:
                                expanded += ['>' if emitted == 0 else '>>', closing[2]]
                            flattened.append((expanded, b, conn))
                            emitted += 1
                    if emitted:
                        w, b, _ = flattened[-1]
                        flattened[-1] = (w, b, parts[j][2])
                    i = j + 1
                    continue
        if words[:1] == ['{']:
            j = i + 1
            while j < len(parts) and parts[j][0][:1] != ['}']:
                j += 1
            if j < len(parts) and len(parts[j][0]) == 3 and parts[j][0][1] == '>':
                target = parts[j][0][2]
                group = [(words[1:], body, connector)] + parts[i+1:j]
                if all(w and w[0] in ('head', 'tail', 'cat', 'echo', 'printf', 'sed')
                       and (b is None or w[0] == 'cat')
                       and not any(x in w for x in ('>', '>>', '|', '<')) for w, b, _ in group):
                    flattened.extend((w + ['>' if n == 0 else '>>', target], b,
                                      parts[j][2] if n == len(group)-1 else ';')
                                     for n, (w, b, _) in enumerate(group))
                    i = j + 1
                    continue
        flattened.append(parts[i])
        i += 1
    for words, body, connector in flattened:
        result.append((words, body, connector, cwd))
        if words and words[0] == 'cd':
            try:
                if len(words) != 2:
                    raise Unknown('cd arguments')
                cwd = resolve_path(words[1], cwd)
            except Unknown:
                cwd = None
        elif words and words[0] in ('pushd', 'popd', 'source', '.'):
            cwd = None
    return result, cwd


def shell_printf(args):
    """Literal printf formats used for source files; no shell evaluation."""
    if not args:
        return ''
    fmt, values = args[0], list(args[1:])
    if '$' in fmt or '`' in fmt:
        raise Unknown('expanded printf')
    def escapes(text):
        def replace(m):
            key = m[1]
            table = {'n': '\n', 't': '\t', 'r': '\r', '\\': '\\', 'a': '\a', 'b': '\b', 'f': '\f', 'v': '\v'}
            if key not in table:
                raise Unknown('printf escape')
            return table[key]
        return re.sub(r'\\(.)', replace, text)
    result = ''
    while True:
        used = 0
        def format_part(m):
            nonlocal used
            if m[1] == '%':
                return '%'
            value = values.pop(0) if values else ''
            used += 1
            if '$' in value or '`' in value:
                raise Unknown('expanded printf argument')
            return escapes(value) if m[1] == 'b' else value
        if re.search(r'%(?![%sb])', fmt):
            raise Unknown('printf conversion')
        # Decode escapes in the format, not in %s argument values.
        result += re.sub(r'%([%sb])', format_part, escapes(fmt))
        if not values or not used:
            return result


def sed_basic_pattern(pattern):
    """Translate the supported BRE subset; reject sed-only constructs."""
    if '[[:' in pattern or '[.' in pattern or '[=' in pattern:
        raise Unknown('sed character class')
    out, i, in_class = '', 0, False
    while i < len(pattern):
        c = pattern[i]
        if c == '\\':
            i += 1
            if i == len(pattern):
                raise Unknown('sed escape')
            c = pattern[i]
            if c in '(){}+?|':
                out += c
            elif c == 'x' and re.fullmatch(r'[0-9a-fA-F]{2}', pattern[i+1:i+3]):
                out += re.escape(chr(int(pattern[i+1:i+3], 16)))
                i += 2
            elif c in '.[]*^$\\' or c in '123456789sSwWbB':
                out += '\\' + c
            elif c in 'nt':
                out += '\\' + c
            else:
                raise Unknown('sed escape')
        else:
            if c == '[':
                in_class = True
            elif c == ']':
                in_class = False
            out += re.escape(c) if c in '(){}+?|' and not in_class else c
        i += 1
    return out


def sed_range(text, start, end, keep=True):
    active, selected = False, []
    for line in text.splitlines(True):
        begins = not active and re.search(sed_basic_pattern(start), line) is not None
        active = active or begins
        if active == keep:
            selected.append(line)
        # A regexp end address is tested starting on the following line.
        if active and not begins and re.search(sed_basic_pattern(end), line):
            active = False
    return ''.join(selected)


def sed_edit(text, script):
    """Apply s/// (BRE), plus numeric line deletion, insertion and replacement."""
    relative_delete = re.fullmatch(r'/([^/]+)/,\+(\d+)d', script)
    if relative_delete:
        remaining, kept = 0, []
        for line in text.splitlines(True):
            if remaining:
                remaining -= 1
            elif re.search(sed_basic_pattern(relative_delete[1]), line):
                remaining = int(relative_delete[2])
            else:
                kept.append(line)
        return ''.join(kept)
    line_delete = re.match(r'^/([^/]+)/d(?:;\s*|$)', script)
    if line_delete:
        pattern = sed_basic_pattern(line_delete[1])
        text = ''.join(line for line in text.splitlines(True) if not re.search(pattern, line.rstrip('\n')))
        rest = script[line_delete.end():]
        return sed_edit(text, rest) if rest else text
    deletion = re.fullmatch(r'/([^/]+)/,/([^/]+)/d', script)
    if deletion:
        return sed_range(text, *deletion.groups(), keep=False)
    address = re.fullmatch(r'(\d+|\$)([diac])(?:\s+|\\)?(.*)', script, re.S)
    if address:
        lines = text.splitlines(True)
        index = len(lines)-1 if address[1] == '$' else int(address[1])-1
        if not 0 <= index < len(lines):
            return text
        if address[2] == 'd' and not address[3]:
            del lines[index]
        elif address[2] in ('i', 'c') and '\\' not in address[3]:
            lines[index:index+(address[2] == 'c')] = [address[3]+'\n']
        elif address[2] == 'a' and '\\' not in address[3]:
            lines.insert(index + 1, address[3]+'\n')
        else:
            raise Unknown('sed line edit')
        return ''.join(lines)
    i = 0
    while i < len(script):
        if script[i] != 's' or i+1 == len(script):
            raise Unknown('sed expression')
        delim = script[i+1]
        i += 2
        parts = []
        for _ in range(2):
            part = ''
            while i < len(script) and script[i] != delim:
                if script[i] == '\\' and i+1 < len(script):
                    nxt = script[i+1]
                    part += nxt if nxt == delim else '\\'+nxt
                    i += 2
                else:
                    part += script[i]; i += 1
            if i == len(script):
                raise Unknown('sed delimiter')
            parts.append(part); i += 1
        end = script.find(';', i)
        end = len(script) if end < 0 else end
        flag = script[i:end].strip()
        old, new = parts
        if not old or flag not in ('', 'g'):
            raise Unknown('sed flag or empty pattern')
        pattern = sed_basic_pattern(old)
        def replacement(match):
            out, j = '', 0
            while j < len(new):
                if new[j] == '&':
                    out += match[0]
                elif new[j] == '\\':
                    j += 1
                    if j >= len(new):
                        raise Unknown('sed replacement escape')
                    c = new[j]
                    if c.isdigit():
                        out += match[int(c)] or ''
                    elif c in 'nt':
                        out += '\n' if c == 'n' else '\t'
                    elif c in '&\\':
                        out += c
                    elif c == 'x' and re.fullmatch(r'[0-9a-fA-F]{2}', new[j+1:j+3]):
                        out += chr(int(new[j+1:j+3], 16)); j += 2
                    else:
                        raise Unknown('sed replacement escape')
                else:
                    out += new[j]
                j += 1
            return out
        text = ''.join(re.sub(pattern, replacement, line.removesuffix('\n'), count=0 if flag else 1)
                       + ('\n' if line.endswith('\n') else '') for line in text.splitlines(True))
        i = end+1
        while i < len(script) and script[i].isspace():
            i += 1
    return text


def replay(command, known, recorded=None, cwd='/workspace', output='', removed=None, depth=0):
    """Return current known contents; also retain successfully reconstructed writes.

    ``recorded`` keeps the last reconstructed version even if a later command
    makes its current contents unknown. It must not be used as current input.
    """
    files = dict(known)
    changed, issues = [], []
    if depth > 5:
        return {}, [], ['nested script limit']
    if inspection_loop(command):
        return files, changed, issues

    # Literal for-loops used to generate small test files. No shell execution.
    loop = re.fullmatch(r'\s*for\s+(\w+)\s+in\s+([\w .\-/]+);\s*do\s+(.*?)\s*done\s*', command, re.S)
    if loop:
        variable, values, body = loop.groups()
        for value in values.split():
            expanded = re.sub(r'\$\{' + re.escape(variable) + r'\}|\$' + re.escape(variable) + r'\b', lambda _: value, body)
            files, writes, problems = replay(expanded, files, recorded, cwd)
            changed.extend(p for p in writes if p not in changed)
            issues.extend(problems)
        return files, changed, issues

    def path(word):
        return resolve_path(word, cwd)

    try:
        commands, _ = command_contexts(command, cwd)
    except (ValueError, Unknown) as e:
        if 'unexpected EOF' in output and 'No closing quotation' in str(e):
            try:
                next(chunks(command))
            except ValueError:
                # Bash could not parse even the first compound command;
                # none of its reads/writes/cd operations ran.
                return files, [], ['Shell syntax error before first command']
        return {}, [], [str(e)]
    blocked = False
    variables = {}
    for command_index, (words, body, connector, cwd) in enumerate(commands):
        if not words:
            continue
        name = words[0]
        before = dict(files)
        try:
            # A parenthesized compiler inspection has no source-file effects.
            if name.startswith('(') and name[1:] in ('coqc', 'rocqc', 'rocq') and '--version' in words:
                continue
            if source_read_only(words):
                # Preserve compilation's conditional-write handling below.
                if name not in ('coqc', 'rocqc', 'rocq', 'coqtop'):
                    continue
            if not blocked and re.fullmatch(r'\w+=\$\(grep', name):
                variable = name.split('=', 1)[0]
                pipe = words.index('|')
                grep_args = words[1:pipe]
                ending = words[pipe+1:]
                if (len(grep_args) == 3 and grep_args[0] == '-n'
                        and ending in (['cut', '-d:', '-f1)'], ['head', '-1', '|', 'cut', '-d:', '-f1)'])):
                    pattern, source = grep_args[1:]
                    matches = [i for i, line in enumerate(files[path(source)].splitlines(), 1)
                               if re.search(sed_basic_pattern(pattern), line)]
                    if matches and (len(matches) == 1 or ending[0] == 'head'):
                        variables[variable] = matches[0]
                        continue
                raise Unknown('unsupported grep assignment')
            expanded = []
            for word in words:
                arithmetic = re.fullmatch(r'\$\(\((\w+)\s*([+-])\s*(\d+)\)\)', word)
                if arithmetic and arithmetic[1] in variables:
                    value = variables[arithmetic[1]]
                    word = str(value + int(arithmetic[3]) * (1 if arithmetic[2] == '+' else -1))
                elif word.startswith('$') and word[1:] in variables:
                    word = str(variables[word[1:]])
                elif word.startswith('+$') and word[2:] in variables:
                    word = '+' + str(variables[word[2:]])
                expanded.append(word)
            words = expanded
            # Common timeout wrapper around compiler/read-only inspection.
            if name == 'timeout' and len(words) > 2 and re.fullmatch(r'\d+[smh]?', words[1]):
                words = words[2:]
                name = words[0]
            if name in ('time', '/usr/bin/time'):
                words = words[1:]
                if words and words[0] == '-p':
                    words = words[1:]
                if words[:1] == ['-f'] and len(words) > 2:
                    words = words[2:]
                name = words[0]
                if name == 'timeout' and len(words) > 2 and re.fullmatch(r'\d+[smh]?', words[1]):
                    words = words[2:]
                    name = words[0]
            # Discard descriptor-only redirects before parsing command operands.
            cleaned, i = [], 0
            while i < len(words):
                if (i + 2 < len(words) and words[i].isdigit()
                        and words[i + 1] in ('>', '>&')
                        and (words[i + 2] == '/dev/null' or words[i + 1] == '>&' and words[i + 2].isdigit())):
                    i += 3
                else:
                    cleaned.append(words[i]); i += 1
            words = cleaned
            if name == 'git' and words[1:2] in (['status'], ['diff'], ['log'], ['ls-files'], ['rev-parse']):
                continue
            if name == 'opam' and words[1:2] in (['list'], ['show']):
                continue
            if name == 'rocqc' and words[1:] == ['--version']:
                continue
            if blocked:
                # Whether a terminal-only message ran cannot change source files.
                # Keep conditional writes blocked, but do not discard known code.
                if source_read_only(words) or (name == 'cd' and len(words) == 2):
                    blocked = connector in ('&&', '||')
                    continue
                raise Unknown('conditional command after unresolved operation')
            if any('$(' in w or '`' in w for w in words):
                raise Unknown('shell command substitution')
            if name == 'cd':
                cwd = path(words[1])
            elif name in ('bash', 'sh') or name.startswith('./'):
                if name.startswith('./'):
                    source = files[path(name)]
                elif words[1:2] == ['-c'] and (len(words) == 3 or words[3:4] == ['|'] and source_read_only(words[4:])):
                    source = words[2]
                elif len(words) == 2:
                    source = files[path(words[1])]
                else:
                    raise Unknown('shell script arguments')
                # Parse recorded script text, never launch a shell process.
                files, writes, problems = replay(source, files, recorded, cwd, output, removed, depth + 1)
                changed.extend(p for p in writes if p not in changed)
                issues.extend(problems)
                if problems and connector == '&&':
                    blocked = True
            elif name in ('python', 'python3'):
                if '__HEREDOC__' in words:
                    source = body
                elif '-c' in words:
                    source = words[words.index('-c') + 1]
                else:
                    source = files[path(words[1])]
                if source is None:
                    raise Unknown('expanded Python script')
                try:
                    argv = words[1:] if '__HEREDOC__' not in words and '-c' not in words else ['-']
                    TextPython(files, cwd, argv).run(source)
                except (ValueError, AssertionError, IndexError, SyntaxError, ZeroDivisionError, ScriptExit) as error:
                    # These are failures of supported Python operations, not
                    # unknown side effects. An index()/assert failure before
                    # open(..., 'w') leaves the source unchanged.
                    issues.append('Python stopped: ' + str(error))
                    blocked = connector == '&&'
            elif name in ('cp', 'mv'):
                operands = [w for w in words[1:] if not w.startswith('-')]
                if len(operands) != 2:
                    raise Unknown('copy operands')
                src, dst = map(path, operands)
                if not posixpath.splitext(dst)[1]:
                    dst = posixpath.join(dst, posixpath.basename(src))
                files[dst] = files[src]
                if name == 'mv':
                    files.pop(src)
            elif name == 'rm':
                for word in words[1:]:
                    if not word.startswith('-'):
                        if '*' in word and not any(c in word for c in '$`~'):
                            pattern = posixpath.normpath(posixpath.join(cwd, word))
                            for target in list(files):
                                if fnmatch.fnmatchcase(target, pattern):
                                    del files[target]
                                    if removed is not None:
                                        removed.add(target)
                            continue
                        p = path(word)
                        if removed is not None:
                            removed.add(p)
                        for target in list(files):
                            if target == p or target.startswith(p.rstrip('/') + '/'):
                                del files[target]
            elif name == 'sed' and '-i' in words:
                script = words[words.index('-i') + 1]
                target = path(words[-1])
                files[target] = sed_edit(files[target], script)
            elif name == 'sed' and any(w.startswith('-i') for w in words[1:]):
                raise Unknown('sed inplace options')
            elif '>' in words or '>>' in words:
                op = '>>' if '>>' in words else '>'
                at = words.index(op)
                # 2>&1 is a descriptor redirect, not a source file write.
                if words[at + 1] == '&':
                    continue
                target = path(words[at + 1])
                args = words[1:at]
                if target == '/dev/null' and name in READ_ONLY:
                    continue
                if name == 'cat' and '__HEREDOC__' in words and body is not None:
                    content = body
                elif name == 'head' and len(args) >= 4 and args[2] == '|' and re.fullmatch(r'-\d+', args[0]):
                    content = ''.join(files[path(args[1])].splitlines(True)[:int(args[0][1:])])
                    if len(args) == 5 and args[3] == 'sed':
                        content = sed_edit(content, args[4])
                    elif len(args) == 5 and args[3] == 'tail' and re.fullmatch(r'-[1-9]\d*', args[4]):
                        content = ''.join(content.splitlines(True)[-int(args[4][1:]):])
                    else:
                        raise Unknown('text pipeline')
                elif name == 'cat' and args:
                    content = ''.join(files[path(w)] for w in args)
                elif name in ('head', 'tail') and args:
                    count = 10
                    if args[0] == '-n':
                        count = int(args[1]); args = args[2:]
                    elif re.fullmatch(r'-\d+', args[0]):
                        count = int(args[0][1:]); args = args[1:]
                    if len(args) != 1:
                        raise Unknown('line selection')
                    lines = files[path(args[0])].splitlines(True)
                    if name == 'head':
                        content = ''.join(lines[:count])
                    elif words[2 if words[1] == '-n' else 1].startswith('+'):
                        content = ''.join(lines[max(0, count-1):])
                    else:
                        content = ''.join(lines[-abs(count):] if count else [])
                elif name == 'printf':
                    content = shell_printf(args)
                elif name == 'awk' and len(args) == 2:
                    stop = re.fullmatch(r'/([^/]+)/\s*\{\s*exit\s*\}\s*\{\s*print\s*\}', args[0])
                    if not stop:
                        raise Unknown('awk selection')
                    lines = []
                    for line in files[path(args[1])].splitlines():
                        if re.search(stop[1], line):
                            break
                        lines.append(line + '\n')
                    content = ''.join(lines)
                elif name == 'sed' and len(args) == 3 and args[0] == '-n':
                    ranges = [re.fullmatch(r'(\d+)(?:,(\d+|\$))?p', x) for x in args[1].split(';')]
                    selection = re.fullmatch(r'(\d+)(?:,(\d+|\$))?p', args[1])
                    pattern_selection = re.fullmatch(r'/([^/]+)/,/([^/]+)/p', args[1])
                    if pattern_selection:
                        content = sed_range(files[path(args[2])], *pattern_selection.groups())
                    elif all(ranges):
                        lines = files[path(args[2])].splitlines(True)
                        content = ''.join(line for i, line in enumerate(lines, 1) for r in ranges
                                          if int(r[1]) <= i <= (len(lines) if r[2] == '$' else int(r[2] or r[1])))
                    elif not selection:
                        raise Unknown('sed line selection')
                    else:
                        lines = files[path(args[2])].splitlines(True)
                        start = int(selection[1])-1
                        stop = len(lines) if selection[2] == '$' else int(selection[2] or selection[1])
                        content = ''.join(lines[start:stop])
                elif name == 'sed' and len(args) == 2:
                    content = sed_edit(files[path(args[1])], args[0])
                elif name == 'echo' and args and not any('$' in w or '`' in w or '\\' in w for w in args):
                    content = ' '.join(args) + '\n'
                else:
                    raise Unknown('output redirection')
                files[target] = (files[target] if op == '>>' else '') + content
            elif name not in READ_ONLY:
                raise Unknown('unsupported command: ' + name)
            elif name in ('env', 'timeout') or any(w in words for w in ('|', '&')) and any(w in words for w in ('tee', 'python3', 'python', 'sh', 'bash')):
                raise Unknown('wrapped command')
            for p, text in files.items():
                if before.get(p) != text:
                    if p not in changed:
                        changed.append(p)
                    if recorded is not None:
                        recorded[p] = text
            if name in ('coqc', 'rocq', 'coqtop') and connector == '&&':
                blocked = True  # exit status of this subcommand is not known
                if command_index + 1 < len(commands):
                    following = commands[command_index + 1][0]
                    if (following[:1] == ['echo'] and len(following) > 1
                            and not any(w in following for w in ('>', '>>', '|', '&'))
                            and not any('$' in w or '`' in w or '\\' in w for w in following[1:])):
                        # A recorded marker proves the conditional branch ran.
                        # It does NOT prove compilation succeeded through a pipe.
                        marker = ' '.join(following[1:])
                        if marker in output.splitlines():
                            blocked = False
        except (Unknown, KeyError, ValueError, TypeError, IndexError, SyntaxError, AttributeError, re.error) as e:
            # No host filesystem, subprocess, imports, exec or eval. If an
            # operation cannot be interpreted, never carry its input forward
            # as if it were still the current source.
            issues.append(str(e))
            targets = write_targets(words, body, cwd, before)
            if targets is None:
                files.clear()
            else:
                for target in targets:
                    files.pop(target, None)
            blocked = connector == '&&'
        if connector == '||':
            blocked = True
    return files, changed, issues
