(** This document is some notes and explanations regarding the [induction] tactic, alongside
    [match] and [Inductive]. *)

(** [Inductive] command *)

(** The [Inductive] command introduced in "IndProp.v" is another method for defining [Prop]s and
    other types aside from [Fixpoint]s. I have discussed previously as part of my notes on the
    [inversion] tactic the comparison between [Fixpoint] and [Inductive] so I won't rehash that
    here, but instead I will focus on an explanation of [Inductive] and their place in Coq's calculus.

    As a matter of fact, all the different types we have encountered in Coq (with the exception of
    function types [A -> B]/[forall (x : A), B]) are introduced using the [Inductive] command
    elsewhere inside the standard library of Coq. This is fundamental to the underlying theory of
    Coq you may have heard mention of before; Coq is based on "CIC" (The Calculus of Inductive
    Constructions) which is an extension of "CoC" (The Calculus of Constructions).

    Without going into detail, CoC only includes function types, variables, and type universes
    such as [Prop] and [Type]. CIC extends CoC with "Inductive Definitions" which is what underlies
    the [Inductive] command as well as the [fix] and [match] term formers in Gallina code. *)

(* Observe that we can print these existing types to see how they are defined using [Inductive]. *)
Print False.
Print True.
Print or.
Print and.

(* As a case study of the syntax of [Inductive] we will look at the [nat] type. *)
Module Nat1.

Print nat.
Inductive (* The [Inductive] command tells Coq that we are going to introduce a new inductive type. *)
  nat (* After the [Inductive] command we must give Coq an identifier for the new type we are introducing. *)
  : (* After the identifier but before the colon ":" we are able to declare parameters to our type.
       (Further details to come later) *)
  Set (* After the colon ":" we must give the "Sort" of our new type. The sort can be a function
         type with indices for new type (Further details to come later) but must end with a type
         universe such as [Prop], [Set], etc. *)
  := (* After the sort we use a ":=" to begin introducing the "constructors" of our new type. [nat]
        has two constructors. *)
(* The constructors of our type are declared one after the other, separated by "|". It is
   conventional to put each constructor on its own line to make the separation clear. *)
| O : nat (* This constructor can be read as: [O : nat] "Zero is a natural number" *)
| S (x : nat) : nat (* This constructor can be read as: For any [x : nat] "[x] which is a natural number",
                    [S x : nat] "[S x] is a natural number" *).

End Nat1.

Module Nat2.

Inductive nat : Set :=
| O : nat
| S : nat -> nat (* It makes no difference whether parameters to our constructors are declared on
                    the left of the colon ":" with names (such as [(x : nat)] above) or on the
                    right of the colon ":" by their type such as [nat -> ...]. *).
(* In both styles the same type with all the same properties is declared. The only superficial
   difference is the names that tactics like [destruct], [inversion], or [induction] will try to
   come up with. If you use a name for an parameters like [(x : nat)] then those tactics will try
   and come up with a name which is some variation on [x] when splitting the goal into cases. *)
End Nat2.

(* Now with more of a handle on the syntax of [Inductive] lets consider the finer details. *)
Module Le1.

Print le. (* We can see that the "less than or equal to" relation is an [Inductive] [Prop] declared
             somewhere in the standard library. *)
Check le : nat -> nat -> Prop. (* Take a moment to understand the relationship between the first
                                  line of the declaration [Inductive le (n : nat) : nat -> Prop ...]
                                  and the type of [le : nat -> nat -> Prop]. *)

(* [le] is a [Prop] which is declared with one parameter [n : nat] and one index of of type [nat].
   Chaining the parameters and indices together gives us the type [le : nat -> nat -> Prop]. *)

(** What then is the difference between parameters of a type and indices of a type?

    Observe bellow that the constructors [le_n] and [le_S] in the declaration are able to refer to
    the parameter [n : nat] by name even though neither of the constructors themselves declare a
    parameter [n : nat].
    On the other hand, the [nat] index of the type needs to be declared as an argument explicitly
    as [forall m : nat, ...] in the [le_S] constructor. *)
Inductive le (n : nat) : nat -> Prop :=
| le_n : le n n
| le_S : forall m : nat, le (S n) m -> le n (S m).

(* If we check the type of the declared constructors we will see that the parameter [n : nat] has
   been added to the front of both types. *)
Check le_n : forall n, le n n.
Check le_S : forall (n : nat)(m : nat), le n m -> le n (S m).

(** Parameters in [Inductive] definitions of types are a convenience for declaring an argument
    which will be included in ALL constructors of that type.
    The rules governing parameters of types is that in every mention in the constructors of the
    type [le] being declared, the parameter [n : nat] must ALWAYS be given unchanged.
    All the mentions of [le] in its constructors are: [le n n], [le n m], and [le n (S m)]. Notice
    that [n] is always given as the first argument of [le] because it is declared as the first
    parameter of [le]. *)

(* As a counterexample here is an erroneous use of a parameter. *)
Fail Inductive bad (n : nat) : Prop :=
| fine : bad n
| wrong : bad (S n) (* The only thing we are allowed to pass as the first argument to [bad] is its
                       parameter [n]. Nothing else. *).

End Le1.

Module Le2.

(** If you want to be able to change the argument passed to mentions of your type in the
    constructors (such as [le n n], [le n m], and [le n (S m)] changing the second argument every
    time) you must declare it as an index not a parameter. *)
Inductive le : nat -> nat -> Prop :=
| le_n : forall n, le n n
| le_S : forall (n m : nat), le n m -> le n (S m).

End Le2.

Module Nat3.

(** To finish the part of this discussion focussing on [Inductive] we return to [Nat].

    Pay special attention to the output of Coq in the [Messages] window of your text editor when
    the following [Inductive] command runs. *)
Inductive nat : Set :=
| O : nat
| S (n : nat) : nat.
(* nat is defined
   nat_rect is defined
   nat_ind is defined
   nat_rec is defined
   nat_sind is defined *)

(** In addition to the declaration that our type [nat] has been defined as a new constant, we are
    also informed that several [nat_X] constants have been defined.

    The one of most interest to us right now is [nat_ind], if you check the types of the others you
    will see that they are all nearly identical except they swap out [Prop] for some other universe.
    I won't discuss the technicalities of that here. *)
Check nat_rect.
Check nat_rec.
Check nat_sind.
Check nat_ind :
  forall (P : nat -> Prop),
    P O ->
    (forall (n : nat), P n -> P (S n)) ->
    forall (m : nat), P m.

(** The type of [nat_ind] should read remarkably similar to the notion of "induction over natural numbers":
    [forall (P : nat -> Prop),] "For all properties of natural numbers P"
    [P O ->] "such that the property P holds at zero, "
    [(forall n, P n -> P (S n)) ->] "and for all natural numbers n such that P holds at n, P also
                                     holds at the successor of n,"
    [forall n, P n] "we can conclude that the property P holds for all natural numbers m."

    The parameter [P : nat -> Prop] is the "motive" of the induction, it is the property that is
    being proven.
    Take note how the parameters after the motive [P] of [nat_ind] align with the constructors of [nat]:
    * [O : nat] becomes [P O].
    * [S (n : nat) : nat] becomes [forall (n : nat), P n -> P (S n)]

    Any parameters of the constructors appear as parameters in the induction principals, and
    parameters of the type being defined [nat] will additionally have an inductive hypothesis added
    for them ([n : nat] both appears as a parameter of the induction principal, and has an
    inductive hypothesis [P n] added as well). *)

(** These "induction principals" are automatically declared by Coq as a convenience are are in fact
    ordinary Coq functions. *)
Print nat_ind.
(* This automatically generated definition may not read how you expected it to so I will build up
   to it in steps. *)

(* Here is how one might've introduced it as a [Fixpoint] function. *)
Fixpoint nat_ind1 (P : nat -> Prop)(H0 : P O)(HS : forall (n : nat), P n -> P (S n))
                  (m : nat) : P m :=
match m with
| O    => H0
| S m' => HS m' (nat_ind1 P H0 HS m')
end.

(* But a [Fixpoint] definition is actually a wrapper around a use of the [fix] term former. *)
Print nat_ind1.

(** [fix] is how ALL recursive functions are declared in Coq.
    Notice the [nat_ind2] argument that just appeared. The name is arbitrary but it is used to make
    any recursive calls. If you are used to anonymous functions like [\x -> ...] in Haskell,
    [lambda x: ...] in Python, or [fun x => ...] in OCaml and Coq, [fix rec x := ...] is extending
    this idea to anonymous recursive functions. *)
Definition nat_ind2 : forall (P : nat -> Prop),
    P O ->
    (forall (n : nat), P n -> P (S n)) ->
    forall (m : nat), P m :=
fix nat_ind2 P H0 HS m := match m with
| O    => H0
| S m' => HS m' (nat_ind2 P H0 HS m')
end.

(** To close the gap between [nat_ind2] and [nat_ind], all of the parameters which never change
    between recursive calls can actually be factored out into a regular [fun] introduction. *)
Print nat_ind.
Definition nad_ind3 : forall (P : nat -> Prop),
    P O ->
    (forall (n : nat), P n -> P (S n)) ->
    forall (m : nat), P m :=
fun P H0 HS => fix nad_ind3 m := match m with
| O    => H0
| S m' => HS m' (nad_ind3 m')
end.

(** Recall of course that all functions in Coq must be terminating. This means that all uses of
    [fix] must be terminating. To check this Coq requires all recursive alls inside of [fix] to be
    on "structurally decreasing" arguments.

    Coq allows us to omit many annotations on the code so long as Coq can infer what they must be
    but I will include the structural annotation bellow to show that Coq is checking that the
    argument of the parameter [m] is "getting smaller" in each recursive call. *)
Definition nad_ind4 : forall (P : nat -> Prop),
    P O ->
    (forall (n : nat), P n -> P (S n)) ->
    forall (m : nat), P m :=
fun P H0 HS =>
  fix nad_ind4 m {struct m} := (* This declares that [m] must be "structurally smaller" in each recursive call *)
  match m with
  | O    => H0
  | S m' => HS m' (nad_ind4 m') (* [m'] comes from "inside" [m] (where [m = S m']) and hence [m']
                                   counts as a smaller argument. *)
  end.

End Nat3.

(** [match] term former *)

(** The syntax of [Inductive] type definitions and [match] statements look very similar, this is
    more than coincidence since the two are complementary notions.

    The [Inductive] command has you declare the name and sort of a new type, followed by listing
    all the ways that type can be constructed, in a list separated by "|" symbols.
    That is to say, an [Inductive] command requires you to declare all the fundamental ways a proof
    of your new type can be introduced.

    The [match] term former has you declare a term (the discriminant) of some inductive type
    (consider [nat] as an example), followed by a list of how the code should proceed based on how
    the discriminant was constructed. One case for each of the constructors of the inductive type.
    That is to say, a [match] term requires you to declare all the ways a proof of the
    discriminants type should be eliminated.

    These two notions of introduction and elimination are mirror images of one another. When
    writing a [match] statement you are obligated to write one branch after the [with] (a branch is
    a line which begins [| <constructor> => <code>]) to handle each of the possible ways the
    discriminant could've been constructed.

    In lieu of an extended discussion of [match] itself, I refer to the reader to the examples in
    the [Nat3] module of this file, as well as the numerous examples in my previous discussions and
    the book chapters themselves. For further discussion don't hesitate to ask in the Discord. *)

(** [induction] tactic *)

(** Where the [destruct] tactic works by introducing a [match] term (as discussed in my
    "Scratchpad.Inversion.v" notes previously) the [induction] tactic works more similarly to
    [apply] by introducing a function call. This is not despite how similar [destruct] and
    [induction] feel to use, but is a consequence of precisely which functions the [induction]
    tactic is applying. By default the [induction] tactic uses one of the [X_ind]/[X_rec] constants
    which are introduced alongside the type by the [Inductive] command and, as seen earlier, these
    induction principals are defined by taking in an argument for what to do in each branch of a
    [match] term. This is why [induction] so closely follows [destruct]. *)

Module Ind1.
(** An invocation of [induction H] proceeds by several steps:
    1. It will follow the same procedure as [generalize dependent H], removing all hypothesise in
       the context which mention [H] and moving them back into the goal along with [H] itself.
    2. Search through the various [X_ind], [X_rec], etc induction principals which were declared at
       the same time as the inductive type of [H], and pick one with the appropriate sort
       (returning a [Prop], or a [Set] etc) to be applied to solve the generalized goal.
    3. A new subgoal is created for each of the remaining parameters of the chosen induction
       principal.
    4. The arguments for each of the branches of the induction are automatically introduced, using
       the names provided by the [... as [H1...|H2...]] syntax if any.

    I have made a small omission which will be addressed later. *)

(* To establish things, here is a typical use of [induction]. *)
Example example1 : forall (x : nat), x * 2 = x + x.
Proof.
  intro x.
  induction x as [|x' IHx'].
  - (* x = 0 *)
    simpl. reflexivity.
  - (* x = S x' *)
    simpl. f_equal. rewrite -> IHx'.
    (* As a bonus, here is some excellent syntax for making the best use of the [Search] command.
       Anything which is named [?x] is a "wildcard" that the search can fill with anything.
       Perfect for finding the lemmas you need. *)
    Search (S (?a + ?b) = ?a + S ?b).
    apply plus_n_Sm.
Qed.

(* We will proceed without using [induction], but instead following the steps laid out above manually. *)
Example example2 : forall (x : nat), x * 2 = x + x.
Proof.
  Check nat_ind.
  intro x.
  generalize dependent x. (* Step 1: Generalize the discriminant [x] *)
  apply nat_ind. (* Step 2: Apply the appropriate induction principal *)
  (* Step 3: New subgoals are created for each branch of the induction *)
  - (* x = 0 *)
    intros. (* Step 4: Introduce the arguments of the branch *)
    simpl. reflexivity.
  - (* x = S x' *)
    intros x' IHx'. (* Step 4: Introduce the arguments of the branch *)
    simpl. f_equal. rewrite -> IHx'. apply plus_n_Sm.
Qed.

(* For completeness we present annotated Gallina code. *)
Example example3 : forall (x : nat), x * 2 = x + x.
Proof
  fun x => (* intro x. *)
  (* [generalize dependent x.] See *1 bellow *)
  nat_ind (fun y => y * 2 = y + y) (* apply nat_ind. *)
  ((* x = 0 *)
   (* [intros.] does nothing in this branch, so no code is created *)
   (* [simpl.] generates no code *)
   eq_refl (* reflexivity. *))
  ((* x = S x' *)
   fun x' IHx' => (* intros x' IHx'. *)
     (* [simpl.] generates no code *)
     f_equal (S) (* f_equal. *)
     (eq_ind_r (fun y => S y = x' + S x') (* rewrite -> IHx'. *)
      (plus_n_Sm x' x') (* apply plus_n_Sm. *)
      IHx'))
    x (* *1: [generalize dependent x.] generates code which applies [x] as an argument *).

(* Gallina code which uses [fix] and [match] directly. *)
Example example4 : forall (x : nat), x * 2 = x + x.
Proof fix rec x := match x with
| 0    => eq_refl
| S x' => f_equal (S)
            (eq_ind_r (fun y => S y = x' + S x')
               (plus_n_Sm x' x')
               (rec x') (* The recursive call [rec x'] plays the roll of [IHx'] in [example3] *))
end.

End Ind1.

Module Ind2.
(** As a more complicated example we return to [le] which is an [Inductive] [Prop] with both
    parameters and indices.

    Returning to the omission I made earlier in regards to the steps of the [induction] tactic.
    It has to do with steps 1 and 4:
    1. It will follow the same procedure as [generalize dependent H], removing all hypothesise in
       the context which mention [H] and moving them back into the goal along with [H] itself.
    4. The arguments for each of the branches of the induction are automatically introduced, using
       the names provided by the [... as [H1...|H2...]] syntax if any.

    I omitted that in addition to the discriminant of the induction [H] being generalized, the
    indices of its type are also generalized. This is also reflected in the induction principals
    Coq generates for such types with indices. *)

(** Notice that the parameter [n : nat] of [le] becomes a parameter of the induction principal,
    declared before [P]. In addition the indices of [le] (the only index is a single [nat]) become
    parameters of the motive [P]. The indices of [le] (the single [nat]) also become parameters of
    the inductive principal right before the discriminant. *)
Check le_ind :
  forall (n : nat) (* The parameter [n : nat] of [le] *)
    (P : nat -> Prop), (* The motive [P : nat -> Prop] of the induction *)
      (* ^^^ - The index [nat] of [le] *)
    P n ->
    (forall (m : nat), le n m -> P m -> P (S m)) ->
    forall (m : nat), le n m -> P m
         (* ^^^^^^^ - The index [nat] of [le] *).

(* An example to demonstrate the index of [le] being generalized during induction. *)
Example example5 : forall (x : nat), le 1 x -> exists y, x = S y.
Proof.
  intros x Hx. induction Hx as [|x' Hx' IHx'].
  (* Notice how in each of the goals, mentions of the index [x] of [Hx : le 1 x] is also changing
     in the contexts of each branch. *)
  - (* Hx = le_n 1, 1 = x *)
    exists 0. reflexivity.
  - (* Hx = le_S x' Hx', S x' = x *)
    exists x'. reflexivity.
Qed.

(* A final example to demonstrate the strength of the generalization done by [induction] and how it
   can manifest in proofs. *)
Example example6 : forall (x : nat), x <> 0 -> le 1 x -> exists y, x = S y.
Proof.
  intros x Ex Hx. (* The hypothesis [Ex] is not needed but we include it to demonstrate the
                     consequences of [x] being generalized by [induction] alongside [Hx]. *)
  induction Hx as [|x' Hx' IHx'].
  - (* Hx = le_n 1, 1 = x *)
    exists 0. reflexivity.
  - (* Hx = le_S x' Hx', S x' = x *)
    (* Notice that [x' <> 0] appears in the type of the inductive hypothesis. This is because the
       original [Ex : x <> 0] depended on the index [x] of [Hx] and hence [Ex] was generalized
       alongside [x] and [Hx]. *)
    exists x'. reflexivity.
Qed.

(* The proof presented without [induction] *)
Example example7 : forall (x : nat), x <> 0 -> le 1 x -> exists y, x = S y.
Proof.
  intros x Ex Hx.
  (* Step 1: Everything depending on the discriminant or its indices is generalized, followed by
     the discriminant and its indices. *)
  generalize dependent Ex. generalize dependent Hx. generalize dependent x.
  (* Step 2: Apply the appropriate induction principal *)
  (* [apply] isn't able to infer the motive of the induction so we supply it *)
  apply (le_ind 1 (fun y => y <> 0 -> exists (z : nat), y = S z)).
  (* Step 3: New subgoals are created for each branch of the induction *)
  - (* Hx = le_n 1, 1 = x *)
    (* Step 4: Introduce the arguments of the branch and reintroduce the generalized hypothesise *)
    intros Ex.
    exists 0. reflexivity.
  - (* Hx = le_S x' Hx', S x' = x *)
    (* Step 4: Introduce the arguments of the branch and reintroduce the generalized hypothesise *)
    intros x' Hx' IHx' Ex.
    exists x'. reflexivity.
Qed.

End Ind2.