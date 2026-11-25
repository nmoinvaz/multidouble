"""The paper's table of Lean proofs (expansion-error-bounds-lean.tex) against the Lean sources: every Lean file at
the top of lean/ExpansionBounds is named in a row, every file a row names exists, and every theorem a row names is
declared in one of that row's files, outside any comment. The modules in the folders under lean/ExpansionBounds
are not read: they hold the kernel's checks and their data, and the files of the rows import them.

usage: lean_refs.py          prints the counts and PASS, or what is wrong
       lean_refs.py check    also the controls, each of which must be reported: a theorem that no file declares, a
                             file that does not exist, a Lean file left out of the table, a theorem inside a
                             comment, one inside a nested comment, one inside a string, one after a string that
                             holds a comment's opening, which must still be found, and a row that TeX comments out"""
import os
import re
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
TEX = os.path.join(HERE, "expansion-error-bounds-lean.tex")
LEAN = os.path.join(HERE, "lean", "ExpansionBounds")
DECL = re.compile(r"^(?:private |noncomputable |protected )*(?:theorem|lemma|def|abbrev|structure)\s+([^\s:({\[]+)", re.M)


def rows(tex):
    """the table's rows as (statement, files, theorems), without what TeX comments out"""
    tex = re.sub(r"(?<!\\)%.*", "", tex)
    body = tex[tex.index(r"\midrule"):tex.index(r"\bottomrule")]
    out = []
    for row in body.split(r"\\"):
        cells = row.split("&")
        if len(cells) != 3:
            continue
        names = [re.findall(r"\\texttt\{([^}]*)\}", c) for c in cells[1:]]
        out.append((" ".join(cells[0].split()), names[0], [n.replace(r"\_", "_") for n in names[1]]))
    return out


def code(text):
    """a Lean source without its comments and the contents of its strings: block comments nest, a line comment runs
    to the end of its line, and a string runs to its closing quote, a backslash escaping the next character"""
    out, depth, i = [], 0, 0
    while i < len(text):
        two = text[i:i + 2]
        if not depth and text[i] == '"':
            i += 1
            while i < len(text) and text[i] != '"':
                if text[i] == "\n":
                    out.append("\n")
                i += 2 if text[i] == "\\" else 1
            i += 1
        elif two == "/-":
            depth, i = depth + 1, i + 2
        elif two == "-/" and depth:
            depth, i = depth - 1, i + 2
        elif depth:
            if text[i] == "\n":
                out.append("\n")
            i += 1
        elif two == "--":
            while i < len(text) and text[i] != "\n":
                i += 1
        else:
            out.append(text[i])
            i += 1
    return "".join(out)


def names(text):
    """the names a Lean source declares"""
    return set(DECL.findall(code(text)))


def declared(folder):
    """the names each Lean file at the top of the folder declares"""
    return {f: names(open(os.path.join(folder, f), encoding="utf-8").read())
            for f in sorted(os.listdir(folder)) if f.endswith(".lean")}


def faults(table, decl):
    """what is wrong with the table, as lines"""
    out = []
    named = set()
    for statement, files, theorems in table:
        named.update(files)
        missing = [f for f in files if f not in decl]
        out += [f"{statement}: no file {f}" for f in missing]
        have = set().union(*(decl[f] for f in files if f in decl)) if files else set()
        out += [f"{statement}: {t} is not declared in {', '.join(files)}" for t in theorems if t not in have]
    out += [f"{f} is in no row" for f in decl if f not in named]
    return out


if __name__ == "__main__":
    table = rows(open(TEX, encoding="utf-8").read())
    decl = declared(LEAN)
    bad = faults(table, decl)
    print(f"{len(table)} statements, {len(decl)} Lean files, {sum(len(r[2]) for r in table)} theorems named")
    print("\n".join(bad) if bad else "every file is named, and every theorem named is declared in its files")
    ok = not bad
    if len(sys.argv) > 1 and sys.argv[1] == "check":
        s, f, t = table[0]
        # the first row's first theorem, in the file that declares it, put inside a comment
        src = next(x for x in f if t[0] in decl[x])
        text = open(os.path.join(LEAN, src), encoding="utf-8").read()
        line = re.search(r"^.*\b(?:theorem|lemma)\s+" + re.escape(t[0]) + r"\b.*$", text, re.M).group(0)
        hidden = [dict(decl, **{src: names(text.replace(line, a + line + b))})
                  for a, b in (("/- ", " -/"), ("/- /- nested -/ ", " -/"))]
        # the same theorem inside a string, and after a string that holds a comment's opening
        quoted = dict(decl, **{src: names(text.replace(line, 'def s : String := "\n' + line + '\n"'))})
        after = names('def s : String := "/-"\n' + line)
        # a row of one line, commented out in the TeX source
        tex = open(TEX, encoding="utf-8").read()
        one = next(x for x in tex[tex.index(r"\midrule"):].splitlines() if x.count("&") == 2 and x.endswith(r"\\"))
        gone = rows(tex.replace(one, "% " + one))
        ctl = [faults([(s, f, t + ["no_such_theorem"])] + table[1:], decl),
               faults([(s, f + ["NoSuchFile.lean"], t)] + table[1:], decl),
               faults(table[1:], decl),
               faults(table, hidden[0]),
               faults(table, hidden[1]),
               faults(table, quoted),
               faults(gone, decl)]
        caught = [any("no_such_theorem" in x for x in ctl[0]), any("NoSuchFile.lean" in x for x in ctl[1]),
                  any("is in no row" in x for x in ctl[2]), any(t[0] + " is not declared" in x for x in ctl[3]),
                  any(t[0] + " is not declared" in x for x in ctl[4]),
                  any(t[0] + " is not declared" in x for x in ctl[5]), t[0] in after,
                  len(gone) == len(table) - 1 and any("is in no row" in x for x in ctl[6])]
        print("controls, a theorem no file declares, a file that does not exist, a file left out, a theorem in a "
              "comment, in a nested comment, in a string, after a string with a comment's opening (found), a row "
              "commented out:", caught)
        ok = ok and all(caught)
    print("PASS" if ok else "FAIL")
    sys.exit(0 if ok else 1)
