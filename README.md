# Deducto

Deducto checks natural deduction proofs written as Scheme data.

It checks each line against its rule and reports the first invalid step.

## Value

Deducto gives immediate, local feedback for logic students and proof authors.

It shows the exact line, rule, and reference that failed.

The REPL builds a proof one checked line at a time.

The hint mode suggests a likely next rule for a target formula.

## Setup

Install Guile 3.0 or newer.

Guile provides the required SRFI libraries, including SRFI-64.

Deducto uses no third-party package dependencies.

Run the test suite:

```text
guile -L src tests/run-tests.scm
```

Check the sample proof:

```text
guile -L src src/main.scm check proofs/valid/implication.scm
```

Use the Unix wrapper when Guile is on your path:

```text
sh bin/deducto check proofs/valid/implication.scm
```

Use `bin/deducto.ps1` from PowerShell.

## Proof format

A proof is a Scheme list with the `proof` marker.

A line contains a formula, a rule, and zero or more references.

A subproof starts with `subproof` and must begin with a `premise`.

A subproof reference uses a dotted pair such as `(1 . 2)`.

References follow the rule order, such as implication then antecedent for `imp-elim`.

```scheme
(proof
  (P premise)
  ((if P Q) premise)
  (Q imp-elim 2 1))
```

Atoms use uppercase symbols.

Predicate arguments use symbols such as `x` or `Ada`.

Connectives use `not`, `and`, `or`, `if`, and `iff`.

Quantifiers use one lowercase variable, as in `(forall (x) (Human x))`.

## Command line

Check a proof and stop at its first invalid line:

```text
guile -L src src/main.scm check FILE
```

Render proof lines with their rules:

```text
guile -L src src/main.scm render FILE
```

Ask for a rule suggestion:

```text
guile -L src src/main.scm hint FILE '(if P Q)'
```

Start the interactive proof builder:

```text
guile -L src src/main.scm repl
```

Build a simple implication in the REPL:

```scheme
(open P)
(step repeat P 1)
(close imp-intro (if P P))
(check)
(quit)
```

## Sample output

```text
Deducto: checking proofs/valid/implication.scm
1. P  ok
2. (if P Q)  ok
3. Q  ok
Result: valid.
```

An invalid line keeps earlier results and explains the first failure.

```text
Deducto: checking proofs/invalid/wrong-repeat.scm
1. P  ok
2. Q  FAIL: repeat must copy line 1, which is P; found Q.
Result: invalid. repeat must copy line 1, which is P; found Q.
```

## Architecture

- `src/deducto/formulas.scm` validates formulas and performs capture-safe substitution.
- `src/deducto/proof.scm` parses nested proofs into numbered lines and spans.
- `src/deducto/check.scm` checks references, rules, scopes, and quantifier freshness.
- `src/deducto/hint.scm` produces deterministic rule suggestions.
- `src/deducto/repl.scm` maintains a checked proof-building session.
- `src/main.scm` provides the command-line interface.

The checker is independent from the command line and REPL.

Tests call the checker and hint modules directly.

## Supported rules

| Area | Rules |
| --- | --- |
| Structure | `premise`, `repeat`, `ex-falso` |
| Propositional | `and-intro`, `and-elim`, `or-intro`, `or-elim` |
| Implication | `imp-intro`, `imp-elim` |
| Negation | `not-intro`, `not-elim` |
| Equivalence | `iff-intro`, `iff-elim` |
| Quantifiers | `forall-intro`, `forall-elim`, `exists-intro`, `exists-elim` |

## Test status

The repository contains deterministic SRFI-64 tests for valid proofs, invalid proofs, scopes, substitution, hints, and the REPL.

Run all tests with `guile -L src tests/run-tests.scm`.

Continuous integration runs the tests, the sample check, and the hint command.

The local verification environment lacked Guile, so this workspace could not execute the Scheme tests.

## Limitations

- Proof files use Scheme data instead of a dedicated text syntax.
- Each quantifier binds one variable.
- Hints use simple pattern matching and do not search the proof space.
- The checker does not discover missing proof lines.
- The rule set does not include equality or modal logic.

## License

Deducto uses the MIT license.