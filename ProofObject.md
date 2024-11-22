## History
In early 1920s, German mathematician Hilbert called for a formalization of all of mathematics in axiomatic form, together with a proof that this axiomatization of mathematics is consistent.

Godel showed that this can not be carried out: Any logical system able to encode arithmetics is inconsistent. This is the famous Godel's Incompleteness Theorem.

Here's a simplified proof of the theorem: Let there be a universal truth machine (the UTM) that evaluates sentences and determines true/false. Since the UTM determines truth, we have sadfasd Now, consider the 
logical sentence `s = UTM always evaluates input sentences as false`. Question: Can we assign `value(s)` a boolean?
1. If `value(s)` is true, then `UTM always evaluates input sentences as false`. Hence, `UTM(s) = false`. But `UTM(s) = value(s)` because UTM determines the truth value of a sentence. So, we have `false = true`, which is inconsistent.
2. If `value(s)` is false, same principle to reach contradiction.

#### The Search
Hence began the search of a consistent system. Untyped lambda calculus (inconsistent because fixpoints exist for every term)=> simply typed (now consistent by disallowing bad untyped terms) => lambda cube (dependent type) => type theory now.


## Proof as Term
(Selections from *Type Theory and Formal Proof* Chapters 2, 5)

Propositions may be viewed as types. This is especially evident in Coq.

```coq
Inductive ev : nat -> Prop :=
  | ev_0                       : ev 0
  | ev_SS (n : nat) (H : ev n) : ev (S (S n)).
```

Here, `ev_0` has type `ev 0`, but `ev_0` is also a proof for the proposition `ev 0`.

What did this look like in simply typed lambda calculus?

Well, we will use abstract propositions $A, B$ instead of `ev 0`. But, for example, consider $\lambda: A . \lambda y: B. x : A \to B \to A$. This shows: The term $\lambda: A . \lambda y: B. x$ inhabits/provides a proof for the logical proposition of $A \to B \to A$. 


The propositions-as-types interpretation of logic also implies another nice and useful interpretation: proofs as terms
- If a term $b$ inhabits type $B$, where $B$ is interpreted as a proposition, then we interpret $b$ as a proof of $B$.
- If no inhabitant of the proposition of $B$ exists, then there exists no proof of $B$, so $B$ is false
- The existence of an inhabitant of type $B$ should be checked in a type system. So to build a proof in a dependent proof assistant, the natural means is to write out a *proof object that has the type of the proof*.


### Dependent Types
When we view the proposition being proved by [ev_plus4] as a
function type in [ev_plus4''], one interesting point becomes apparent: The second
argument's type, [ev n], mentions (depends on) the _value_ of the first argument, [n].

```coq
Theorem ev_plus4 : forall n, ev n -> ev (4 + n).
Definition ev_plus4' : forall n, ev n -> ev (4 + n)
Definition ev_plus4'' (n : nat) (H : ev n): ev (4 + n)
```

In general, "[P -> Q]" is just syntactic sugar for
    "[forall (_:P), Q]".

### Logical Connectives as Inductive Types
Only universal quantification (with implication as a special case) is built into Coq, 
all connectives are defined inductively.

```coq
Inductive and (P Q : Prop) : Prop :=
  | conj : P -> Q -> and P Q.

Inductive or (P Q : Prop) : Prop :=
  | or_introl : P -> or P Q
  | or_intror : Q -> or P Q.

Inductive ex {A : Type} (P : A -> Prop) : Prop :=
  | ex_intro : forall x : A, P x -> ex P.
```

### Examining `exists`
```coq
Inductive ex {A : Type} (P : A -> Prop) : Prop :=
  | ex_intro : forall x : A, P x -> ex P.
```

The `forall` keyword might seem confusing: How are we defining `exists` with `forall`?

The key is to realize coq uses `forall` for:
1. Logical universal quantification (in propositions)
2. Dependent function types (in type signatures)

Here, the second kind of `forall` is used. Hence, as long as there is some 
`x: A` that has `P x`, then we have `ex P`.

### True, False
[False] is an inductive type with _no_ constructors --
    i.e., no way to build evidence for it.
```coq
Inductive False : Prop := .
```
Since there are no branches to evaluate, the [match] expression
    can be considered to have any type we want, including [0 = 1].
```coq
Definition false_implies_zero_eq_one : False -> 0 = 1 :=
  fun contra => match contra with end.
```

### Unsynthesized
The following might not make sense. Seeing how rudienmentary `eq_refl` is, it doesn't make sense that `eq (2 + 2) (1 + 3)`.
The trick is: Coq treats as "the same" any two terms that are convertible according to a simple set of computation rules 
(evaluation of function application, definition inlining, and match simplification).

```coq
Lemma four: 2 + 2 == 1 + 3.
Proof.
  apply eq_refl.
Qed.
```

In proof object form, this is:
```coq
Definition four' : 2 + 2 == 1 + 3 :=
  eq_refl 4.
```

### Unsynthesized
In general, the [inversion] tactic...

- takes a hypothesis [H] whose type [P] is inductively defined,
  and
- for each constructor [C] in [P]'s definition,
  - generates a new subgoal in which we assume [H] was
    built with [C],
  - adds the arguments (premises) of [C] to the context of
    the subgoal as extra hypotheses,
  - matches the conclusion (result type) of [C] against the
    current goal and calculates a set of equalities that must
    hold in order for [C] to be applicable,
  - adds these equalities to the context (and, for convenience,
    rewrites them in the goal), and
  - if the equalities are not satisfiable (e.g., they involve
    things like [S n = O]), immediately solves the subgoal.


### Unsynthesized
One question that arises with any automated proof assistant
    is "why should we trust it?" -- i.e., what if there is a bug in
    the implementation that renders all its reasoning suspect?

    While it is impossible to allay such concerns completely, the fact
    that Coq is based on the Curry-Howard correspondence gives it a
    strong foundation. Because propositions are just types and proofs
    are just terms, checking that an alleged proof of a proposition is
    valid just amounts to _type-checking_ the term.  Type checkers are
    relatively small and straightforward programs, so the "trusted
    computing base" for Coq -- the part of the code that we have to
    believe is operating correctly -- is small too.

### Unsynthesized: Trusted Computaing Base
Why should we trust an automated proof assistant? What if there is a bug in the implementation that renders all its reasoning suspect?

Because propositions are just types and proofs are just terms, checking that an allged proof of a proposition is valid just amounts to type-checking the term. Type checkers are relatively small and straightforward programs, so the "trusted computing base" for Coq is small too.

The typechecker is to make sure that expected and actual argument types match, that the arms of a [match] expression are constructor patterns belonging to the inductive type being matched over and all arms of the [match] return the same type, and so on. Additionally, the checker will perform normalization on expressions and also that recursive function terminates.

### Unsynthesized: Propositional Extensionality
Propositional extensionality overlooks syntactical differences just as functional extensionality overlooks syntactic differences between functions.

```coq
Definition propositional_extensionality : Prop :=
  forall (P Q : Prop), (P <-> Q) -> P = Q.
```

Propositional Extensionality implies Proof Irrelevance.