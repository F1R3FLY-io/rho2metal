#!/usr/bin/env python3
"""rhoc: compiler from the stage 1 fragment of the source language to ROM
images for the tile array (design specification draft 0.6, Sections 3, 4
and 7).

Concrete syntax
    P ::= Nil | P "|" P | x!(Q) | for(p <- x) P | for(p <- x where C) P
        | for(p <= x) P | for(p <= x where C) P | B | A | *x | (P) | {P}
    B ::= true | false | *x | ~B | B && B | B || B | B xor B
    A ::= n | *x | -A | A + A | A - A | A * A
    C ::= B | A cmp A | ~C | C && C | C || C      cmp: < <= == != >= >
    x ::= identifier | @Nil | @true | @false | @n | @(closed expression)
    p ::= v | @d      d ::= Nil | true | false | n | v | Boolean or
                           arithmetic operators over these

The null process is written Nil; 0 is the numeral.

Stage 1 limits, each rejected with a message: payloads are values (no
quoted sends or receives); patterns are shallow; a clause compares
operands, not compound terms, and has at most two atoms; / and % are not
available; integers are 29 bits wide.
"""
import json
import re
import sys

IW = 29
IMASK = (1 << IW) - 1
E = 6
K = 6
T_ZERO, T_BOOL, T_INT, T_SYM = 0, 1, 2, 3


def word(tag, pay=0):
    return (tag << 29) | (pay & IMASK)


class CompileError(Exception):
    pass


# ----------------------------------------------------------------- lexer
TOKEN = re.compile(r"""\s*(?:(?P<num>\d+)|(?P<id>[A-Za-z_][A-Za-z0-9_']*)|
    (?P<op><-|<=|>=|==|!=|&&|\|\||[-+*~!@(){}|<>]))""", re.X)
KEYWORDS = {"for", "where", "Nil", "true", "false", "xor"}


def lex(src):
    src = re.sub(r"//[^\n]*", "", src)
    out, i = [], 0
    while True:
        while i < len(src) and src[i].isspace():
            i += 1
        if i >= len(src):
            break
        m = TOKEN.match(src, i)
        if not m:
            raise CompileError("cannot read: %r" % src[i:i + 12])
        i = m.end()
        if m.group("num"):
            out.append(("num", int(m.group("num"))))
        elif m.group("id"):
            s = m.group("id")
            out.append(("kw" if s in KEYWORDS else "id", s))
        else:
            out.append(("op", m.group("op")))
    out.append(("eof", None))
    return out


# ---------------------------------------------------------------- parser
class Parser:
    def __init__(self, toks):
        self.t, self.i = toks, 0

    def peek(self):
        return self.t[self.i]

    def take(self):
        tok = self.t[self.i]
        self.i += 1
        return tok

    def accept(self, kind, val=None):
        k, v = self.peek()
        if k == kind and (val is None or v == val):
            self.i += 1
            return True
        return False

    def expect(self, kind, val=None):
        if not self.accept(kind, val):
            raise CompileError("expected %s, found %r" % (val or kind, self.peek()[1]))

    # processes
    def proc(self):
        p = self.term()
        while self.accept("op", "|"):
            p = ("par", p, self.term())
        return p

    def term(self):
        k, v = self.peek()
        if k == "kw" and v == "for":
            self.take()
            self.expect("op", "(")
            pat = self.pattern()
            if self.accept("op", "<-"):
                persistent = False
            elif self.accept("op", "<="):
                persistent = True
            else:
                raise CompileError("expected <- or <= after the pattern")
            chan = self.name()
            clause = None
            if self.accept("kw", "where"):
                clause = self.expr()
            self.expect("op", ")")
            return ("recv", pat, chan, clause, persistent, self.term())
        if k == "kw" and v == "Nil":
            self.take()
            return ("nil",)
        if k == "op" and v == "{":
            self.take()
            p = self.proc()
            self.expect("op", "}")
            return p
        # a send starts with a name followed by "!"
        save = self.i
        if (k == "id") or (k == "op" and v == "@"):
            try:
                nm = self.name()
                if self.accept("op", "!"):
                    self.expect("op", "(")
                    if self.peek() == ("kw", "Nil"):
                        self.take()
                        pay = ("nilv",)
                    else:
                        pay = self.expr()
                    self.expect("op", ")")
                    return ("send", nm, pay)
            except CompileError:
                pass
            self.i = save
        if k == "op" and v == "(":
            # a parenthesised process, unless it reads as an expression
            save = self.i
            self.take()
            try:
                p = self.proc()
                self.expect("op", ")")
                if self.peek()[1] not in ("&&", "||", "+", "-", "*", "xor"):
                    return p
            except CompileError:
                pass
            self.i = save
        return ("evalp", self.expr())

    def name(self):
        if self.accept("op", "@"):
            k, v = self.take()
            if k == "kw" and v == "Nil":
                return ("qlit", ("nilv",))
            if k == "kw" and v in ("true", "false"):
                return ("qlit", ("bool", v == "true"))
            if k == "num":
                return ("qlit", ("num", v))
            if k == "op" and v == "(":
                e = self.expr()
                self.expect("op", ")")
                return ("qlit", e)
            raise CompileError("unsupported quoted name")
        k, v = self.take()
        if k != "id":
            raise CompileError("expected a name, found %r" % (v,))
        return ("ident", v)

    def pattern(self):
        if self.accept("op", "@"):
            if self.accept("kw", "Nil"):
                return ("pzero",)
            self.pmode = True
            e = self.unary()
            self.pmode = False
            return ("pquote", e)
        k, v = self.take()
        if k != "id":
            raise CompileError("expected a pattern")
        return ("pquote", ("pvar", v))

    pmode = False

    # expressions, loosest first
    def expr(self):
        e = self.xor_()
        while self.accept("op", "||"):
            e = ("or", e, self.xor_())
        return e

    def xor_(self):
        e = self.and_()
        while self.accept("kw", "xor"):
            e = ("xor", e, self.and_())
        return e

    def and_(self):
        e = self.cmp_()
        while self.accept("op", "&&"):
            e = ("and", e, self.cmp_())
        return e

    def cmp_(self):
        e = self.add()
        k, v = self.peek()
        if k == "op" and v in ("<", "<=", "==", "!=", ">=", ">") and not self.pmode:
            self.take()
            return ("cmp", v, e, self.add())
        return e

    def add(self):
        e = self.mul()
        while True:
            if self.accept("op", "+"):
                e = ("add", e, self.mul())
            elif self.accept("op", "-"):
                e = ("sub", e, self.mul())
            else:
                return e

    def mul(self):
        e = self.unary()
        while self.accept("op", "*"):
            e = ("mul", e, self.unary())
        return e

    def unary(self):
        if self.accept("op", "~"):
            return ("not", self.unary())
        if self.accept("op", "-"):
            return ("neg", self.unary())
        if self.accept("op", "*"):
            return ("drop", self.name())
        if self.accept("op", "("):
            e = self.expr()
            self.expect("op", ")")
            return e
        k, v = self.take()
        if k == "num":
            return ("num", v)
        if k == "kw" and v in ("true", "false"):
            return ("bool", v == "true")
        if k == "id" and self.pmode:
            return ("pvar", v)
        raise CompileError("unexpected %r in an expression" % (v,))


BOOL_OPS = {"not", "and", "or", "xor", "bool"}
ARITH_OPS = {"neg", "add", "sub", "mul", "num"}


def sort_of(e):
    """'bool', 'int', or None for a bare drop or pattern variable."""
    if e[0] in BOOL_OPS:
        return "bool"
    if e[0] in ARITH_OPS:
        return "int"
    if e[0] == "cmp":
        return "clause"
    return None


def leaves(e):
    if e[0] in ("drop", "pvar"):
        yield e
    elif e[0] in ("num", "bool", "nilv"):
        return
    else:
        for c in e[1:]:
            if isinstance(c, tuple):
                yield from leaves(c)


# -------------------------------------------------------------- compiler
class Compiler:
    def __init__(self):
        self.cnodes = [None]          # address 0 is the root
        self.xnodes = []
        self.rinfos = []
        self.syms = {}
        self.nil = None

    # names and operands ------------------------------------------------
    def sym(self, s):
        if s not in self.syms:
            self.syms[s] = len(self.syms)
        return word(T_SYM, self.syms[s])

    def lit_word(self, e):
        if e[0] == "nilv":
            return word(T_ZERO)
        v = self.const(e)
        if v is None:
            raise CompileError("a quoted name must be closed")
        return v

    def name_opnd(self, nm, scope):
        if nm[0] == "qlit":
            return {"k": 1, "w": self.lit_word(nm[1])}
        if nm[1] in scope:
            return {"k": 0, "w": scope.index(nm[1])}
        return {"k": 1, "w": self.sym(nm[1])}

    def const(self, e):
        """Value of a closed Boolean or arithmetic expression, or None."""
        if e[0] == "num":
            return word(T_INT, e[1])
        if e[0] == "bool":
            return word(T_BOOL, int(e[1]))
        if any(True for _ in leaves(e)):
            return None
        if sort_of(e) == "bool":
            return word(T_BOOL, int(self.bool_eval(e, {})))
        if sort_of(e) == "int":
            return word(T_INT, self.int_eval(e, {}))
        return None

    def bool_eval(self, e, env):
        op = e[0]
        if op == "bool":
            return e[1]
        if op in ("drop", "pvar"):
            return env[self.leaf_key(e)]
        if op not in ("not", "and", "or", "xor"):
            raise CompileError("a number or an arithmetic operator inside a Boolean expression")
        if op == "not":
            return not self.bool_eval(e[1], env)
        a, b = self.bool_eval(e[1], env), self.bool_eval(e[2], env)
        if op == "and":
            return a and b
        if op == "or":
            return a or b
        if op == "xor":
            return a != b
        raise CompileError("an arithmetic operator inside a Boolean expression")

    def int_eval(self, e, env):
        op = e[0]
        if op == "num":
            return e[1] & IMASK
        if op in ("drop", "pvar"):
            return env[self.leaf_key(e)]
        if op == "neg":
            return (-self.int_eval(e[1], env)) & IMASK
        if op not in ("add", "sub", "mul"):
            raise CompileError("a Boolean operator inside an arithmetic expression")
        a, b = self.int_eval(e[1], env), self.int_eval(e[2], env)
        return {"add": a + b, "sub": a - b, "mul": a * b}[op] & IMASK

    @staticmethod
    def leaf_key(e):
        return e[1][1] if e[0] == "drop" else e[1]

    # expressions ---------------------------------------------------------
    def expr_x(self, e, scope):
        """Compile a payload or residue expression; return its address."""
        if e[0] == "nilv":
            return self.emit_x({"kind": 0, "a": {"k": 1, "w": word(T_ZERO)}})
        if e[0] == "cmp" or any(c[0] == "cmp" for c in self.walk(e)):
            raise CompileError("a comparison may occur only in a where clause")
        c = self.const(e)
        if c is not None:
            return self.emit_x({"kind": 0, "a": {"k": 1, "w": c}})
        if e[0] == "drop":
            return self.emit_x({"kind": 0, "a": self.name_opnd(e[1], scope)})
        if sort_of(e) == "bool":
            sup, table = self.truth_table(e, scope)
            if not sup:
                return self.emit_x({"kind": 0, "a": {"k": 1, "w": word(T_BOOL, table & 1)}})
            if len(sup) == 1 and table == 0b10:
                return self.emit_x({"kind": 0, "a": {"k": 0, "w": sup[0]}})
            return self.emit_x({"kind": 1, "k": len(sup), "sup": sup, "table": table})
        steps = []
        self.arith_steps(e, scope, steps)
        if len(steps) > 8:
            raise CompileError("an arithmetic expression of more than eight operators")
        addr = len(self.xnodes)
        for i, s in enumerate(steps):
            s["last"] = int(i == len(steps) - 1)
            self.xnodes.append(s)
        return addr

    def walk(self, e):
        yield e
        for c in e[1:]:
            if isinstance(c, tuple):
                yield from self.walk(c)

    def emit_x(self, n):
        self.xnodes.append(n)
        return len(self.xnodes) - 1

    def bool_leaf_index(self, e, scope):
        nm = e[1]
        if nm[0] != "ident" or nm[1] not in scope:
            raise CompileError("a Boolean operand must be the drop of a variable")
        return scope.index(nm[1])

    def truth_table(self, e, scope):
        """Minimal ordered support (de Bruijn indices) and truth table."""
        idx = sorted({self.bool_leaf_index(l, scope) for l in leaves(e)})
        names = {i: scope[i] for i in idx}

        def value(assign):
            return self.bool_eval(e, {names[i]: assign[i] for i in idx})
        # drop variables on which the function does not depend
        keep = []
        for v in idx:
            dep = False
            others = [i for i in idx if i != v]
            for r in range(1 << len(others)):
                a = {o: bool((r >> j) & 1) for j, o in enumerate(others)}
                if value({**a, v: False}) != value({**a, v: True}):
                    dep = True
                    break
            if dep:
                keep.append(v)
        if len(keep) > K:
            raise CompileError("a Boolean expression depends on more than %d variables" % K)
        table = 0
        for r in range(1 << len(keep)):
            a = {i: False for i in idx}
            a.update({v: bool((r >> j) & 1) for j, v in enumerate(keep)})
            if value(a):
                table |= 1 << r
        return keep, table

    def arith_operand(self, e, scope, steps):
        c = self.const(e) if not any(True for _ in leaves(e)) else None
        if c is not None:
            return {"k": 1, "w": c}
        if e[0] == "drop":
            return self.name_opnd(e[1], scope)
        self.arith_steps(e, scope, steps)
        return {"k": 2, "w": len(steps) - 1}

    def arith_steps(self, e, scope, steps):
        op = e[0]
        if op not in ("add", "sub", "mul", "neg"):
            raise CompileError("a Boolean operator inside an arithmetic expression")
        a = self.arith_operand(e[1], scope, steps)
        b = self.arith_operand(e[2], scope, steps) if op != "neg" else {"k": 1, "w": word(T_INT, 0)}
        steps.append({"kind": 2, "op": {"add": 0, "sub": 1, "mul": 2, "neg": 3}[op], "a": a, "b": b})

    # patterns ------------------------------------------------------------
    def pattern(self, pat):
        """Return (receive-info fields, variables in binding order, the
        set of variables a clause may not mention, the mask variables)."""
        info = {"pkind": 0, "nmask": 0, "btable": 0, "c0": 0, "c1": 0, "c2": 0,
                "k": 0, "t": 0, "pivot": 0, "oinv": 1}
        if pat[0] == "pzero":
            info["pkind"] = 1
            return info, [], set(), []
        d = pat[1]
        if d[0] == "pvar":
            return info, [d[1]], set(), []
        s = sort_of(d)
        if s == "bool":
            mvars = []
            for l in leaves(d):
                if l[1] not in mvars:
                    mvars.append(l[1])
            if len(mvars) > K:
                raise CompileError("a pattern with more than %d mask variables" % K)
            table = 0
            for r in range(1 << len(mvars)):
                if self.bool_eval(d, {v: bool((r >> j) & 1) for j, v in enumerate(mvars)}):
                    table |= 1 << r
            info.update(pkind=2, nmask=len(mvars), btable=table)
            return info, mvars, set(), mvars
        if s == "int":
            unk = []
            for l in leaves(d):
                if l[1] not in unk:
                    unk.append(l[1])
            if len(unk) > 2:
                raise CompileError("an arithmetic leaf with more than two unknowns")
            zero = {v: 0 for v in unk}
            c0 = self.int_eval(d, zero)
            coef = []
            for v in unk:
                c = (self.int_eval(d, {**zero, v: 1}) - c0) & IMASK
                coef.append(c)
            # the leaf must be affine: check it against a few assignments
            for trial in ((3, 5), (7, 2), (IMASK, 11)):
                a = {v: trial[j] for j, v in enumerate(unk)}
                want = (c0 + sum(c * a[v] for c, v in zip(coef, unk))) & IMASK
                if self.int_eval(d, a) != want:
                    raise CompileError("an arithmetic leaf that is not affine")
            if any(c == 0 for c in coef):
                raise CompileError("an unknown with coefficient zero")
            info.update(pkind=3, c0=c0, k=len(unk))
            free = set()
            if unk:
                val = [(c & -c).bit_length() - 1 for c in coef]
                t = min(val)
                pivot = val.index(t)
                odd = coef[pivot] >> t
                info.update(c1=coef[0], c2=coef[1] if len(unk) > 1 else 0, t=t,
                            pivot=pivot, oinv=pow(odd, -1, 1 << IW))
                if not (len(unk) == 1 and t == 0):
                    free = set(unk)
            return info, unk, free, []
        raise CompileError("unsupported pattern")

    # clauses -------------------------------------------------------------
    def clause(self, c, scope, nvars, mvars, free):
        """Compile a clause to atoms and a table over mask rows and atoms."""
        atoms = []

        def operand(e):
            v = self.const(e) if not any(True for _ in leaves(e)) else None
            if v is not None:
                return {"k": 1, "w": v}
            if e[0] == "drop":
                nm = e[1]
                if nm[0] == "ident" and nm[1] in free:
                    raise CompileError("a clause mentions an unknown the pattern does not determine")
                if nm[0] == "ident" and nm[1] in mvars:
                    raise CompileError("a Boolean variable used as a number in a clause")
                return self.name_opnd(nm, scope)
            raise CompileError("in stage 1 a clause compares operands, not compound terms")

        def atom(op, a, b):
            key = (op, json.dumps(a, sort_keys=True), json.dumps(b, sort_keys=True))
            for i, (k2, _) in enumerate(atoms):
                if k2 == key:
                    return i
            atoms.append((key, {"op": op, "a": a, "b": b}))
            return len(atoms) - 1

        def build(e):
            """Return a function from (row, atom bits) to a truth value."""
            op = e[0]
            if op == "bool":
                return lambda row, ab: e[1]
            if op == "not":
                f = build(e[1])
                return lambda row, ab: not f(row, ab)
            if op in ("and", "or", "xor"):
                f, g = build(e[1]), build(e[2])
                if op == "and":
                    return lambda row, ab: f(row, ab) and g(row, ab)
                if op == "or":
                    return lambda row, ab: f(row, ab) or g(row, ab)
                return lambda row, ab: f(row, ab) != g(row, ab)
            if op == "drop":
                nm = e[1]
                if nm[0] == "ident" and nm[1] in mvars:
                    j = mvars.index(nm[1])
                    return lambda row, ab: bool((row >> j) & 1)
                i = atom(2, operand(e), {"k": 1, "w": 0})
                return lambda row, ab: bool((ab >> i) & 1)
            if op == "cmp":
                a, b = operand(e[2]), operand(e[3])
                rel = e[1]
                if rel in (">", "<="):
                    a, b = b, a                       # a > b is b < a; a <= b is not (b < a)
                if rel in ("<", ">", "<=", ">="):
                    i = atom(0, a, b)
                    neg = rel in ("<=", ">=")
                else:
                    a, b = sorted((a, b), key=lambda o: json.dumps(o, sort_keys=True))
                    i = atom(1, a, b)
                    neg = rel == "!="
                return lambda row, ab: bool((ab >> i) & 1) != neg
            raise CompileError("unsupported term in a clause")

        f = build(c)
        nm = len(mvars)
        rows = range(1 << nm)
        # keep only the atoms on which the function depends
        keep = []
        for i in range(len(atoms)):
            if any(f(r, ab) != f(r, ab ^ (1 << i)) for r in rows for ab in range(1 << len(atoms))):
                keep.append(i)
        if nm + len(keep) > K:
            raise CompileError("a clause depends on more than %d things" % K)
        if len(keep) > 2:
            raise CompileError("in stage 1 a clause has at most two atoms")
        table = 0
        for ab in range(1 << len(keep)):
            full = 0
            for j, i in enumerate(keep):
                full |= ((ab >> j) & 1) << i
            for r in rows:
                if f(r, full):
                    table |= 1 << ((ab << nm) | r)
        if not keep and table == (1 << (1 << nm)) - 1:
            return None                               # the clause is true
        return {"atoms": [atoms[i][1] for i in keep], "table": table}

    # processes -----------------------------------------------------------
    def emit_c(self, n, at=None):
        if at is None:
            self.cnodes.append(n)
            return len(self.cnodes) - 1
        self.cnodes[at] = n
        return at

    def proc(self, p, scope, at=None):
        op = p[0]
        if op == "nil":
            if at is None:
                if self.nil is None:
                    self.nil = self.emit_c({"kind": 0})
                return self.nil
            return self.emit_c({"kind": 0}, at)
        if op == "par":
            x = self.proc(p[1], scope)
            y = self.proc(p[2], scope)
            return self.emit_c({"kind": 1, "x": x, "y": y}, at)
        if op == "send":
            return self.emit_c({"kind": 2, "chan": self.name_opnd(p[1], scope),
                                "x": self.expr_x(p[2], scope)}, at)
        if op == "evalp":
            return self.emit_c({"kind": 4, "x": self.expr_x(p[1], scope)}, at)
        if op == "recv":
            _, pat, chan, clause, persistent, body = p
            info, bound, free, mvars = self.pattern(pat)
            for v in bound:
                if bound.count(v) > 1:
                    raise CompileError("variable %s bound twice" % v)
            inner = list(reversed(bound)) + scope
            if len(inner) > E:
                raise CompileError("more than %d variables in scope" % E)
            info["persist"] = int(persistent)
            info["nvars"] = len(bound)
            g = self.clause(clause, inner, len(bound), mvars, free) if clause is not None else None
            info["guard"] = g
            ri = len(self.rinfos)
            self.rinfos.append(info)
            node = self.emit_c({"kind": 3, "chan": self.name_opnd(chan, scope), "x": ri}, at)
            info["body"] = self.proc(body, inner)
            return node
        raise CompileError("unsupported process")


# ------------------------------------------------------------- packing
def pack(fields):
    v, n = 0, 0
    for val, width in fields:
        v = (v << width) | (val & ((1 << width) - 1))
        n += width
    return v, n


def opnd(o):
    o = o or {"k": 1, "w": 0}
    return [(o["k"], 2), (o["w"], 32)]


def pack_c(n):
    n = n or {"kind": 0}
    return pack([(n["kind"], 3)] + opnd(n.get("chan")) + [(n.get("x", 0), 8), (n.get("y", 0), 8)])


def pack_x(n):
    n = n or {"kind": 0}
    sup = 0
    for i, s in enumerate(n.get("sup", [])):
        sup |= s << (3 * i)
    return pack([(n["kind"], 2), (n.get("last", 0), 1), (n.get("op", 0), 3), (n.get("k", 0), 3),
                 (sup, 18)] + opnd(n.get("a")) + opnd(n.get("b")) + [(n.get("table", 0), 64)])


def pack_r(r):
    if r is None:
        r = {"persist": 0, "body": 0, "pkind": 0, "nmask": 0, "btable": 0, "c0": 0, "c1": 0,
             "c2": 0, "k": 0, "t": 0, "pivot": 0, "oinv": 0, "guard": None}
    g = r["guard"]
    atoms = (g["atoms"] if g else []) + [{"op": 0, "a": None, "b": None}] * 2
    f = [(r["persist"], 1), (r["body"], 8), (r["pkind"], 2), (r["nmask"], 3), (r["btable"], 64),
         (r["c0"], 29), (r["c1"], 29), (r["c2"], 29), (r["k"], 2), (r["t"], 5), (r["pivot"], 1),
         (r["oinv"], 29), (1 if g else 0, 1), (len(g["atoms"]) if g else 0, 2)]
    for a in atoms[:2]:
        f += [(a["op"], 2)] + opnd(a["a"]) + opnd(a["b"])
    f.append((g["table"] if g else 0, 64))
    return pack(f)


def write_rom(path, items, depth, packer):
    with open(path, "w") as fh:
        for i in range(depth):
            v, n = packer(items[i] if i < len(items) else None)
            fh.write("%0*x\n" % ((n + 3) // 4, v))


def compile_source(src):
    p = Parser(lex(src))
    ast = p.proc()
    if p.peek()[0] != "eof":
        raise CompileError("unexpected %r" % (p.peek()[1],))
    c = Compiler()
    c.proc(ast, [], at=0)
    if len(c.cnodes) > 256 or len(c.xnodes) > 256 or len(c.rinfos) > 64:
        raise CompileError("the program does not fit the stage 1 static segment")
    return {"cnodes": c.cnodes, "xnodes": c.xnodes, "rinfos": c.rinfos, "syms": c.syms}


def write_image(img, outdir):
    write_rom(outdir + "/romc.hex", img["cnodes"], 256, pack_c)
    write_rom(outdir + "/romx.hex", img["xnodes"], 256, pack_x)
    write_rom(outdir + "/romr.hex", img["rinfos"], 64, pack_r)
    with open(outdir + "/image.json", "w") as fh:
        json.dump(img, fh, indent=1)


if __name__ == "__main__":
    if len(sys.argv) != 3:
        sys.exit("usage: rhoc.py SOURCE.rho OUTDIR")
    try:
        write_image(compile_source(open(sys.argv[1]).read()), sys.argv[2])
    except CompileError as err:
        sys.exit("rhoc: " + str(err))
