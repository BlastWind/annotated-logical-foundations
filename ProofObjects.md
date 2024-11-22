## ProofObjects

#### Proposition as Types
We have seen hints that Coq's programming and proving facility are closely related.
For example, the keyword `[Inductive]` is used to declare both data types and propositions,
and `[->]` is used both the describe the types of functions and logical implication. 

This is NOT a syntactic accident! In fact, programs and proofs in Coq are almost the samething.

Fundamentally, provability in Coq is represented by concrete evidence. When we construct
the proof of a basic proposition, we are actually building a tree of evidence.

If the proposition is an implication like `[A -> B]`, then its proof will be an evidence
transformer: a recipe for converting evidence for `[A]` into evidence for `[B]`. So,
proofs are programs that manipulate evidence.

Now, if evidences are data, what are proposition themselves?

They are types!

For example, in

```coq
Inductive ev : nat -> Prop :=
  | ev_0                       : ev 0
  | ev_SS (n : nat) (H : ev n) : ev (S (S n)).
```

Here are some sound statements:
1. `[ev_0]` has the dependent type `[ev 0]`.
2. `[ev_0]` is a proof for / is evidence for `[ev 0]`.
3. `[ev_SS]` has the dependent type `ev (S (S n))` given a proof of / evidence of `ev n`.
4. `[ev_SS]` is a proof for `ev (S (S n))` given a proof of / evidence of `ev n`.

We see the correspondance here.

Type ~ Proposition
- `[ev_0]` is a proof for and has the dependent type `[ev 0]`.

Proof ~ Data Values

TODO.

#### Evidence Constructor
`ev_SS` can be thought of as a primitive "evidence constructor". When applied to a particular number, 
wants to further applied to evidence that this 
number is even. Its type reflect this:

```
forall n, ev n -> ev (S (S n))
```

in the same way that the polymorphic type `[forall X, list X]` expresses the fact that `[nil]` can be thought of as a function from types to empty lists with elements of that type. (I don't understand this).

#### Proof Script
When Coq is following a proof script, it is gradually constructing a proof object, 
a term whose type is the proposition being proved.

We could use `Theorem name . Proof Type . Tactics Proof. Qed.`, but we can also do `Definition name : Proof Type := Proof Object`.


#### Quantifiers, Implications, Functions
Both logical implication `([->])` and quantification (`[forall]`) correspond to type theory functions on evidences. They are in fact the same: `[->]` is a shorthand for a degenerated use of [forall] where there is no dependency.

`[P -> Q]` is just syntactic sugar for `[forall (_:P), Q]`.

#### Programming with Tactics
We can build programs using tactics rather than writing down explicit terms.

```coq
Definition add1: nat -> nat.
intro n.
apply S.
apply n.
Defined.
```

Accordingly, this feature is mainly useful for writing functions with dependent types.

#### Logical Connectives as Inductive Types
**Only universal quantification (with implication as a special case) is built into Coq; all 
other connectives are defined inductively**.

```coq
Inductive and (P Q : Prop) : Prop :=
  conj : P -> Q -> P /\ Q.

Inductive prod (X Y : Type) : Type :=
  pair : X -> Y -> X * Y.
```

Definition of `and_comm'` is extremely interesting:
```coq
Definition and_comm'_aux P Q (H : P /\ Q) : Q /\ P :=
  match H with
  | conj HP HQ => conj HQ HP
  end.

Definition and_comm' P Q : P /\ Q <-> Q /\ P :=
  conj (and_comm'_aux P Q) (and_comm'_aux Q P).
```

It's worth noting the following:
```coq
Definition or_commut' : forall P Q, P \/ Q -> Q \/ P :=
  fun P Q => fun HPQ =>
    match HPQ with
    | or_introl HP => or_intror HP
    | or_intror HQ => or_introl HQ
    end.
```
Question: What's the difference between `HP` and `P`?
Answer: With `HP`, we get to assume `P`. `P` is just a proposition.