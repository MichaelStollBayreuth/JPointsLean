# The correspondence with the C code

Lean has no semantics of C, so the link between the model in `JPoints/Model` and the C code of
`j-points` is a record of which Lean declaration models which lines of C, checked by
`scripts/correspondence.py`, together with the differential tests.

## The pin

Every line number refers to one commit of `j-points`, the pin in
[`j-points.toml`](j-points.toml): release 3.0.2, commit `3633f63`. The C code is read with
`git show <commit>:<file>`, so the working tree of the C repository may be at any commit.

## The ranges

The record covers the files listed in `j-points.toml`: `j-points.c`, `j-sift.c` and `j-points.h`.
A line of code is a line that holds something outside comments (a preprocessor line counts; a
blank line, or one that holds only a comment, does not). Every line of code of the files lies in
exactly one recorded range, which is either

- **modeled**: the docstring of a public declaration of the model names it in a paragraph of its
  own,

  ```lean
  /-- `CEIL(a, b)` of `j-points.h`, `⌈a / b⌉` for `b > 0`, by the truncating division of C.

  C: `j-points.h:48` -/
  def ceilDiv (a b : Int) : Int := if a ≤ 0 then -((-a).tdiv b) else 1 + (a - 1).tdiv b
  ```

  with one or more items `` `file:first-last` `` (or `` `file:line` ``) separated by commas. A
  range cited by several declarations is one range with several names. An optional `Deviation:`
  paragraph says where the model departs from the C code (an `Int` for a `long`, with the
  obligations of its range as lemmas, an index for a pointer, the bits of a double with a model
  function for each operation on it, the sequential order for the threads). A private declaration
  cannot carry the record (a blueprint node cannot name it), and `check` reports one that does; a
  docstring that `@[inherit_doc]` lends to a notation or an alias is not the declaration's own and
  makes no record; or

- **excluded**: an `[[excluded]]` table of `j-points.toml` gives the range, a kind and the reason.
  The kinds are threads (the threads of `-t`, whose output is that of one thread), memory (the
  allocation and release of memory and of the GMP variables, and the failures for lack of
  memory), instrumentation (the output under `DEBUG` and `VERBOSE`, and the debug build), interface
  and other (the headers, the forward declarations, the vector builds `VW > 1`, and code that has
  no effect in the build modeled). The build modeled is the default one: `DEBUG = 0`, `VERBOSE`
  undefined, the scalar walk `VW = 1`, on an LP64 platform.

Two different ranges must not overlap, and every range holds a line of code. When a declaration
calls another that models part of its C code, it cites the lines around that part, not the whole
function. A line that the model needs stays with the model even where most of it would be excluded
(the brace that opens a loop together with the declaration of a scratch variable, say).

## The checks

`scripts/correspondence.py check` builds the model, reads the docstrings of its declarations with
`scripts/Correspondence.lean`, and checks

- that the pinned commit exists (and the tag, where the repository has it, points to it), that
  every C file of the record exists there, and that every range lies in a listed file, within its
  lines, and holds a line of code;
- that no line lies in two different ranges;
- that the excluded ranges have a known kind and a reason, and that no private declaration and no
  copied docstring carries a record;
- that every range was reviewed with its present text and its present counterpart: `lock.json`
  holds, for each range, the SHA-256 of its text at the pin and its owners (the declarations that
  model it, or its exclusion), and the hash of the text of each C link of the blueprint;
  `scripts/correspondence.py lock` writes it after the review of what `check` reported. A new range,
  a range whose counterpart changed (to another declaration, from an exclusion to a declaration, or
  a declaration added to a shared range) and a new link are reported until they are locked;
- that the generated chapter of the blueprint, `blueprint/src/generated/correspondence.tex` (the
  table from C to Lean, which also lists any lines of code that no range records), is up to date
  (`scripts/correspondence.py table` regenerates it), that the blueprint's `\jpointscommit` is the
  pin, that every `\csource{file}{first}{last}` is a range of a listed file, and that every C link
  of a node of the dependency graph (the environments of the `thms=` option of the blueprint package
  in `web.tex`, by default definition, lemma, proposition, theorem and corollary) that names
  declarations with `\lean{…}` is a range of one of the model declarations it names. A node need not
  cite every range of its declarations, and a model declaration need not be named by a node: the
  generated chapter lists every range with its owners. Prose and other environments, such as
  remarks, may link to any range;
- with `--complete`, that every line of code lies in a range: a line that no declaration models
  and no exclusion covers fails the check. Without `--complete` the check ignores such lines.

`scripts/correspondence.py coverage` lists the stretches of lines of code not recorded, file by
file; `scripts/correspondence.py table` writes the generated chapter of the blueprint (or the file
that `--output` names; `--output -` writes to the standard output).

The script needs a clone of `j-points` that contains the pin, given by `--repo PATH` or the
environment variable `JPOINTS_REPO`. With `--decls FILE` it reads the docstrings from a file that
`scripts/Correspondence.lean` wrote (the environment variable `CORRESPONDENCE_DECLS` names it)
instead of building the model itself.

## Moving the pin

When the project moves to a new `j-points` release, the line numbers move with the C code:

1. run `scripts/correspondence.py move --to <commit> --tag <tag>`: it sets the new commit and tag
   in `j-points.toml` and `\jpointscommit` in the blueprint, and moves every C range cited in the
   tracked text files (the docstrings, the excluded tables, the blueprint's links and the READMEs)
   to its lines at the new commit, by `git diff -U0`; it lists each range that a hunk of the diff
   touched, and leaves a range whose lines are all gone as it was;
2. fix by hand what it lists as gone, and check what it lists as touched;
3. run `scripts/correspondence.py table` and then `check`: since the lock still names the old
   commit, `check` accepts a range whose text and owners some locked range has (it moved but did
   not change) and a link whose text some locked link has, and reports exactly the others, which
   are new or changed;
4. review those against their Lean counterparts (and fix the model where the C code changed),
   record the new lines of code, which `scripts/correspondence.py coverage` lists, in the model or
   as exclusions, and then run `scripts/correspondence.py lock`.

Until the last step `check` fails, naming the lock's old commit.
