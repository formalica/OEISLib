"""Renders `Equiv_<hash>.lean` files and their validation modules."""

from __future__ import annotations

import re
from dataclasses import dataclass, field

from .config import CHECK_LIB, OEISLib_LIB

SEQ_REF = re.compile(r"\bA\d{6}\b")

FORBIDDEN_KEYWORDS = ("import ", "namespace ", "section ", "#eval", "#check", "#print")

#: Namespace holding the data-backed stand-ins used to execute a translation whose
#: dependencies still have `sorry` bodies.
SHIM_NS = "_root_.Oeis.Check.Shim"


@dataclass
class SeqInfo:
    """Everything the renderer needs about one sequence."""

    name: str
    title: str
    offset: int
    terms: list[str]

    @property
    def bucket(self) -> str:
        return self.name[:4]

    @property
    def ret_type(self) -> str:
        return "Int" if any(t.startswith("-") for t in self.terms) else "Nat"

    @property
    def main_arg_kind(self) -> str:
        if self.offset == 0:
            return "Nat"
        if self.offset == 1:
            return "PNat"
        if self.offset > 1:
            return "NatSub"
        return "IntSub"

    @property
    def main_arg_type(self) -> str:
        return arg_type_str(self.main_arg_kind, self.offset)

    @property
    def allowed_arg_kinds(self) -> list[str]:
        if self.offset < 0:
            return ["Int", "IntSub"]
        if self.offset == 0:
            return ["Nat"]
        if self.offset == 1:
            return ["Nat", "PNat", "NatSub"]
        return ["Nat", "NatSub"]

    def module(self, suffix: str) -> str:
        return f"{OEISLib_LIB}.{self.bucket}.{self.name}.{suffix}"


def arg_type_str(kind: str, offset: int) -> str:
    if kind == "Nat":
        return "Nat"
    if kind == "PNat":
        return "PNat"
    if kind == "Int":
        return "Int"
    if kind == "NatSub":
        return f"{{n : Nat // {offset} ≤ n}}"
    if kind == "IntSub":
        return f"{{n : Int // {offset} ≤ n}}"
    raise ValueError(f"unknown arg_kind {kind!r}")


def coerce_main_index(main_kind: str, formula_kind: str) -> str:
    """Expression of type `formula`'s argument type, written in terms of `n : main argType`."""
    table = {
        ("Nat", "Nat"): "n",
        ("PNat", "Nat"): "(n : Nat)",
        ("PNat", "PNat"): "n",
        ("PNat", "NatSub"): "⟨(n : Nat), n.property⟩",
        ("NatSub", "Nat"): "n.val",
        ("NatSub", "NatSub"): "n",
        ("IntSub", "Int"): "n.val",
        ("IntSub", "IntSub"): "n",
    }
    key = (main_kind, formula_kind)
    if key not in table:
        raise ValueError(f"arg_kind {formula_kind!r} is not allowed for a {main_kind!r} sequence")
    return table[key]


def index_literal(kind: str, index: int, offset: int) -> str:
    """`formula`'s argument for the OEIS index `index`."""
    lit = f"({index})" if index < 0 else str(index)
    if kind == "Nat":
        return f"({lit} : Nat)"
    if kind == "PNat":
        return f"({lit} : PNat)"
    if kind == "Int":
        return f"({lit} : Int)"
    if kind == "NatSub":
        return f"(⟨{lit}, by norm_num⟩ : {{n : Nat // {offset} ≤ n}})"
    if kind == "IntSub":
        return f"(⟨{lit}, by norm_num⟩ : {{n : Int // {offset} ≤ n}})"
    raise ValueError(f"unknown arg_kind {kind!r}")


def sanitize_doc(text: str) -> str:
    """OEIS text is free-form and may contain Lean comment delimiters."""
    return text.replace("-/", "- /").replace("/-", "/ -")


def referenced_sequences(text: str, own_name: str) -> list[str]:
    return sorted({m for m in SEQ_REF.findall(text) if m != own_name})


def shim_substitute(code: str) -> str:
    """Redirects every `Axxxxxx...` reference to its data-backed stand-in."""
    return SEQ_REF.sub(lambda m: f"{SHIM_NS}.{m.group(0)}", code)


def dep_shim_text(dep: SeqInfo, owner: str) -> str:
    """Executable stand-in for one dependency, built from the terms OEIS knows.

    Out-of-range indices `panic!` with a marker the pipeline greps for, so a translation
    that reaches past the known data is reported as such instead of as a wrong formula."""
    ret = dep.ret_type
    terms = ", ".join(f"({t})" if t.startswith("-") else t for t in dep.terms)
    coe = {
        "Nat": "(n : Int)",
        "PNat": "((n : Nat) : Int)",
        "NatSub": "(n.val : Int)",
        "IntSub": "n.val",
    }[dep.main_arg_kind]
    return "\n".join(
        [
            f"/-- Known terms of `{dep.name}`, indexed from `{dep.offset}`. -/",
            f"def {dep.name}.data : List {ret} := [{terms}]",
            "",
            f"def {dep.name}.fz (n : Int) : {ret} :=",
            f"  let i := n - ({dep.offset} : Int)",
            f"  if 0 ≤ i ∧ i < ({dep.name}.data.length : Int) then {dep.name}.data[i.toNat]!",
            f'  else panic! s!"OEIS_DEP_RANGE {owner} needs {dep.name} n={{n}}"',
            "",
            f"def {dep.name}.fn (n : Nat) : {ret} := {dep.name}.fz (n : Int)",
            "",
            f"def {dep.name} : {dep.main_arg_type} → {ret} := fun n => {dep.name}.fz {coe}",
        ]
    )


def checkable_terms(seq: SeqInfo, deps: list[str], dep_seqs: dict[str, SeqInfo],
                    max_terms: int) -> int:
    """How many terms can be validated: a shim only knows its own sequence up to the
    last index OEIS lists, and `a(n)` usually needs its dependencies at indices up to `n`."""
    count = min(max_terms, len(seq.terms))
    for name in deps:
        dep = dep_seqs.get(name)
        if dep is None:
            continue
        last = dep.offset + len(dep.terms) - 1
        count = min(count, max(0, last - seq.offset + 1))
    return count


def validate_lean_code(code: str) -> str | None:
    """Returns an error message when the model broke the code-shape contract."""
    if not re.search(r"^\s*(noncomputable\s+)?def\s+formula\b", code, re.MULTILINE):
        return "lean_code does not define `formula` (expected a line starting with `def formula`)"
    if len(re.findall(r"^\s*(?:noncomputable\s+)?def\s+formula\b", code, re.MULTILINE)) > 1:
        return "lean_code defines `formula` more than once"
    for kw in FORBIDDEN_KEYWORDS:
        for line in code.splitlines():
            if line.lstrip().startswith(kw.strip()) and kw.strip() != "namespace":
                return f"lean_code must not contain `{kw.strip()}`; the pipeline adds it"
            if kw.strip() == "namespace" and line.lstrip().startswith("namespace "):
                return "lean_code must not open a namespace; the pipeline adds it"
    for line in code.splitlines():
        stripped = line.lstrip()
        if stripped.startswith("theorem ") or stripped.startswith("lemma "):
            return "lean_code must not contain theorems; only `formula` and helper defs"
    return None


@dataclass
class RenderedItem:
    """A model item that passed validation, together with its generated files."""

    seq: SeqInfo
    formula_hash: str
    original_text: str
    lean_code: str
    arg_kind: str
    computable: bool
    note: str = ""
    deps: list[str] = field(default_factory=list)
    span_start: int = 0
    span_end: int = 0
    start_marker: str = ""
    end_marker: str = ""
    equiv_module: str = ""
    check_module: str = ""
    equiv_path: str = ""
    check_path: str = ""
    checked_terms: int = 0

    @property
    def namespace(self) -> str:
        return f"{self.seq.name}.Equiv_{self.formula_hash}"

    @property
    def key(self) -> str:
        return f"{self.seq.name}:{self.formula_hash}"


def equiv_file_text(item: RenderedItem, dep_seqs: dict[str, SeqInfo]) -> str:
    seq = item.seq
    imports = [f"import {seq.module('Defs')}"]
    for dep in item.deps:
        if dep in dep_seqs:
            imports.append(f"import {dep_seqs[dep].module('Defs')}")
    formula_arg = arg_type_str(item.arg_kind, seq.offset)
    coe = coerce_main_index(seq.main_arg_kind, item.arg_kind)
    header = "\n".join(
        [
            "/-!",
            f"# {seq.name} — alternative definition `Equiv_{item.formula_hash}`",
            "",
            f"{sanitize_doc(seq.title)}",
            "",
            "Machine translation of one Maple program of the OEIS entry.",
            "",
            "Original Maple source:",
            "",
            *[f"    {sanitize_doc(line)}" for line in item.original_text.splitlines()],
            "",
            f"Chosen index type: `{formula_arg}`. Value type: `{seq.ret_type}`.",
            "-/",
        ]
    )
    body = item.lean_code.strip("\n")
    return "\n".join(
        [
            *imports,
            "",
            header,
            "",
            f"namespace {item.namespace}",
            "",
            body,
            "",
            "/-- The formalized Maple program agrees with the main definition. -/",
            f"theorem formula_eq (n : {seq.name}.argType) :",
            f"    formula {coe} = {seq.name} n := sorry",
            "",
            f"end {item.namespace}",
            "",
        ]
    )


def check_file_text(item: RenderedItem, batch_id: int, dep_seqs: dict[str, SeqInfo],
                    max_terms: int) -> str:
    """Validation module: evaluates the translation against the terms OEIS knows.

    The `Equiv_` module is imported so its own elaboration errors surface, but the values
    are computed from a local copy of the code. That copy is needed because a translation
    calling another sequence cannot be executed through the real `Axxxxxx.fn`, whose body
    is still `sorry`; the copy is redirected to data-backed shims instead.
    """
    seq = item.seq
    ns = f"{CHECK_LIB}.B{batch_id}.{seq.name}_{item.formula_hash}"
    imports = [
        f"import {CHECK_LIB}.Basic",
        f"import {seq.module('Equiv_' + item.formula_hash)}",
    ]
    count = checkable_terms(seq, item.deps, dep_seqs, max_terms)
    terms = seq.terms[:count]
    args = [index_literal(item.arg_kind, seq.offset + i, seq.offset) for i in range(count)]
    expected = ", ".join(f"({t})" if t.startswith("-") else t for t in terms)

    prelude: list[str] = []
    if item.deps:
        prelude.append(f"namespace {SHIM_NS.removeprefix('_root_.')}")
        prelude.append("")
        for dep in item.deps:
            if dep in dep_seqs:
                prelude.append(dep_shim_text(dep_seqs[dep], seq.name))
                prelude.append("")
        prelude.append(f"end {SHIM_NS.removeprefix('_root_.')}")
        prelude.append("")

    code = shim_substitute(item.lean_code) if item.deps else item.lean_code
    actual = ",\n   ".join(f"((formula {a} : {seq.ret_type}) : Int)" for a in args)
    return "\n".join(
        [
            *imports,
            "",
            "/-! Generated validation module; deleted once the batch is recorded. -/",
            "",
            *prelude,
            f"namespace {ns}",
            "",
            code.strip("\n"),
            "",
            f'#eval Oeis.Check.report "{seq.name}" ({seq.offset})',
            f"  [{expected}]",
            f"  [{actual}]",
            "",
            f"end {ns}",
            "",
        ]
    )
