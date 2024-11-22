(** This document is some notes and explanations regarding the discussion following the "IndProp.v"
    chapter.
    Specifically discussion with regards to [bool] vs. [Prop] (via Fixpoint) vs.
    [Prop] (via Inductive). *)

Require Setoid.

(** Discussion of [bool] vs [Prop]. *)

(** In the "Logic.v" chapter a short discussion was included in the book of the differences between
    the [bool] type and the [Prop] universe. The primary difference highlighted by by the book is
    that members of the [bool] type are all decidable (in an empty context they evaluate to either
    [true] or [false]) whereas members of the [Prop] universe are not (in an empty context they
    evaluate to some type).

    I believe this is the first time the word "universe" has been used explicitly so I'll give a
    short definition. A "universe" like [Prop] is a "type of types", in other languages like
    Haskell they may be referred to as "kinds" instead of "universes". *)

Print bool.
Module Bool.

(** For documentation I have repeated the definition of [bool] here. *)
Inductive bool : Set :=
| true | false.

End Bool.

Reserved Notation "x =? y" (at level 70).

Fixpoint eqb (x y : nat) : bool :=
match x, y with
| 0  , 0   => true
| S x, S y => x =? y
| _  , _   => false
end where
"x =? y" := (eqb x y) : nat_scope.

Check Prop. (* [Prop : Type] where [Type] is another "universe" which has [Prop] as a member. *)
Check Type.
Check 1 = 2. (* [1 = 2 : Prop] where [1 = 2] is the type of proofs that [1] is identical to [2] and [Prop] is the "universe" of such types. *)
Check bool. (* [bool : Set] where [Set] is another "universe" which has [bool] as a member. *)
Check 1 =? 2. (* [1 =? 2 : bool] where [bool] is a type with two members [true] and [false]. *)
Compute negb true. (* We will be using [negb] later so this is a reminder it exists. *)

(** The significance of this distinction between [Prop]s and [bool]s makes itself known when
    variables of each appear in proofs. *)

(** When a proof is stuck on a [bool] expression it is possible to use [destruct] on the expression
    and continue the proof with the assumption that the [bool] is [true] or [false] respectively. *)
Lemma bool_example1 : forall {A : Prop}(x : bool), (x = true -> A) -> (x = false -> A) -> A.
Proof.
  intros A x Htrue Hfalse.
  destruct x as [|] eqn:Ex. (* [x : bool], [x] is a member of [bool] which is a type introduced by
                               the [Induction] command. Therefor is can be used in the [destruct] tactic. *)
  - (* [x = true] *)
    apply Htrue. reflexivity.
  - (* [x = false] *)
    apply Hfalse. reflexivity.
Qed.

Search eq_refl.

Definition example (A : Prop) (x : bool) (Htrue : x = true -> A) (Hfalse : x = false -> A) :=
  (match x as y return x = y -> A with
  | true  => Htrue
  | false => Hfalse
  end).

Check example.


(** The same can of course be done directly, without the use of tactics. *)
Lemma bool_example2 : forall {A : Prop}(x : bool), (x = true -> A) -> (x = false -> A) -> A.
Proof fun A x Htrue Hfalse =>
(** [destruct x [|] eqn:Ex.] translates into a [match] expression.
    The [... as y return x = y -> A] part of the expression may be unfamiliar to you. I won't
    explain it in detail here but feel free to ask me in Discord. A short explanation is that when
    [x] is matched on in the code mentions of [x] in the types of [Htrue] and [Hfalse] aren't
    replaced with [true] or [false] as they are by [destruct x as [|] eqn:Ex.]. *)
match x as y return x = y -> A with
| true  => Htrue
| false => Hfalse
end eq_refl.

(** When a proof is stuck of a [Prop] expression it is not possible to use [destruct] in the same
    way as [bool] expressions. *)
Lemma Prop_example1 : forall {A : Prop}(X : Prop), (X -> A) -> (~X -> A) -> A.
Proof.
  intros X Htrue Hfalse.
  (* destruct X as [|] eqn:EX. *)
Abort.

(** The reason this is not allowed is perhaps clearer when trying to write the code directly.

    There are *infinitely* many possible members of [Prop] that would have to be considered in a
    theoretical [match] expression on a [Prop], as such it is impossible to "decide" which specific
    [Prop] is given as the argument for [X]. *)
Lemma Prop_example2 : forall {A : Prop}(X : Prop), (X -> A) -> (~X -> A) -> A.
Proof (* fun X Htrue Hfalse =>
match X with
| True          => _
| False         => _
| eq 1 2        => _
| True \/ False => _
| True /\ False => _
| ...
end *).
Abort.

(** This insight into [Prop] raises a question:
    "How is it that that [Prop] variables can be used at all?".

    The "Logic.v" chapter demonstrated this by numerous examples but I will try to give a perhaps
    more explicit explanation here. *)
Lemma Prop_example3 :
  forall {A : Prop}(X : Prop), (X <-> True) \/ (X <-> False) ->
    (X -> A) -> (~X -> A) -> A.
Proof.
  intros A X HX Htrue Hfalse.
  (** The key to working with [Prop] variables is the operations that are provided to you as hypothesise.
      When working with [Prop] variables the only operations it is possible to perform are:
      1. Ones given to you as hypothesise.
      2. Other lemmas which take [Prop] arguments. *)
  destruct HX as [H1|H1] eqn:EX.
  - (* [X] is provable *)
    apply Htrue. rewrite -> H1. reflexivity.
  - (* [X] is not provable *)
    apply Hfalse. rewrite -> H1. intro contra. apply contra.
Qed.

(** Working with [Prop] arguments is more general than working with [bool] arguments precisely
    because there is more to [Prop]s than just being [true] (provable) or [false] (not provable).

    "What more is there besides not being decidable?"
    [bool] is a very simple type, the only thing that can be said about [bool] expressions is that
    they evaluate to [true] or [false], nor matter how detailed or specific the [bool] expression.
    [Prop]s on the other hand say more, a member of a [Prop] is a term which explains *how* that
    [Prop] can be proven, and a non-provable [Prop] is one which has no way to construct a term at
    its type.
    In this way a proof of a [Prop] gives you more information than a proof of a [bool]. A proof of
    a [bool] only declares that the statement is [true] or [false], whereas a proof of a [Prop] can
    be destructed on to get more details of *why* it is true. *)

(** I will use evenness from "IndProp.v" to further the discussion of the differences between
    [bool] and [Prop] in proofs. *)

(** [Fixpoint] definition of an even test. *)
Fixpoint even (x : nat) : bool :=
match x with
| 0 => true
(* This match could be nested inside the first. I have nested them to make it clear that two steps
   of matching are happening for each recursive call. *)
| S x' => match x' with
          | 0     => false
          | S x'' => even x''
          end
end.

(** Lets prove what we would hope is a trivial fact:
    The predecessor of an even number is odd. *)
Theorem even_Sx__even_x_fail :
  forall (x : nat), even (S x) = true -> even x = false.
Proof.
  (* Our statement is a property of natural numbers,
     so perhaps we proceed by an induction on the [nat]? *)
  induction x as [|x' IHx].
  - (* [x = 0] *) discriminate.
  - (* [x = S x'] *)
    (* [simpl] does not improve things as much as we'd hope.
       The reason is that [even] matches on its argument twice,
       so perhaps we should discriminate on the argument?  *)
    destruct x' as [|x''].
    + (* [x' = 0] [x = S 0] *) reflexivity.
    + (* [x' = S x''] [x = S (S x'')] *)
      (* A quick aside to cleanup our context *)
      assert (forall y, even (S (S y)) = even y) as Estep.
      { reflexivity. }
      rewrite -> Estep. rewrite -> Estep. rewrite -> Estep in IHx.

      (* The inductive hypothesis seems to be in the right form to allow us to make progress. *)
      rewrite -> IHx. { discriminate. }
      (* Our goal state seems to be stuck on a [bool],
         so lets try [destruct] on the [bool]? *)
      destruct (even x'').
      * reflexivity.
      (* Finally we seem completely stuck so we'll give up on this approach. *)
      * admit.
Abort.

(** The fact that [even] matches on its argument twice just caused us a lot of grief since
    [induction] on [nat]s only allows us to proceed by one step at a time (as far as we understand
    it right now).

    How should be go about proving our fact than? We need to come up with some clever lemma that
    implies our fact; a lemma we are able to prove by induction over [nat]s one step at a time.
    [even_negb] is what I have chosen for this example. *)

(** We will need the fact that [negb] is involutive in our proof of [even_negb]. *)
Theorem negb_involutive : forall (x : bool), negb (negb x) = x.
Proof. destruct x. - reflexivity. - reflexivity. Qed.

(* Here we state our lemma. It should feel similar in spirit to our original fact, the difference
   being that our two uses of [even] are being related directly by an equality rather than
   indirectly by [bool]. *)
Lemma even_negb : forall (x : nat), even (S x) = negb (even x).
Proof.
  (* As before we are proving a property of [nat]s,
     so lets attempt induction of the [nat] argument. *)
  induction x as [|x' IHx'].
  - (* [x = 0] *) reflexivity.
  - (* [x = S x'] *)
    (* We defer to the inductive hypothesis to continue the proof. *)
    rewrite -> IHx'.
    (* The nested [negb] calls cancel each other. *)
    rewrite -> negb_involutive.
    reflexivity.
Qed.

(* Finally we can reattempt proving our fact. *)
Theorem even_Sx__even_x :
  forall (x : nat), even (S x) = true -> even x = false.
Proof.
  (* We are proving a property of [nat]s,
     however we now know that [induction] will get us into trouble. *)
  destruct x as [|x'].
  - (* [x = 0] *) discriminate.
  - (* [x = S x'] *)
    intro Eeven. simpl in Eeven.
    (* Our lemma makes it possible to rewrite by our hypothesis. *)
    rewrite -> even_negb.
    rewrite -> Eeven. reflexivity.
Qed.

(* As an extra challenge you may want to try and prove [even_Sn__even_n] directly by induction
   without deferring to [even_negb]. Although I believe the separation of [even_negb] from
   [even_Sn__even_n] is a useful one. *)

(** Having proven [even_Sn__even_n] with [bool]s let's now investigate using a [Prop] to prove it. *)

(** [Fixpoint] definition of a doubling operation. *)
Fixpoint double (x : nat) : nat :=
match x with
| 0 => 0
| S x => S (S (double x))
end.

(** [Definition] introduction of an even proposition. *)
Definition Even (x : nat) : Prop := exists y, x = double y.

(** While we are not able to destruct on a variable of type [Prop], [Even x] is not a variable,
    and we are able to destruct on it to understand why [x] is even in greater detail. *)

Theorem Even_Sx__Even_x : forall (x : nat), Even (S x) -> ~Even x.
Proof.
  induction x as [|x' IHx'].
  - (* [x = 0] *)
    intro HEven.
    (* [EEven]s claim [Even 1] is immediately suspicious,
       destructing on it will reveal *why* in greater detail. *)
    destruct HEven as [y Ey].
    (* The claim that there is a [y] such that [1 = double y] is dubious,
       so we continue our investigation there. *)
    destruct y as [|y'].
    + (* [y = 0] *) simpl in Ey. discriminate.
    + (* [y = S y'] *) simpl in Ey. discriminate.
  - (* [x = S x'] *)
    intros HEven HSx'.
    (* Our goal is a proof of [False] and none of our hypothesise are obviously contradictory.
       However we can use our inductive hypothesis to prove [False]. *)
    apply IHx'. { apply HSx'. }
    (* Our goal is a proof of [Even x'].
       Unfolding [Even] may make it clearer what our exact proof obligations are. *)
    unfold Even.
    (* [Goal : exists y : nat, x' = double y]
       Our hypothesis [HEven : Even (S (S x'))] will hopefully provide
       evidence of a suitable [y] if we destruct it. *)
    destruct HEven as [y Ey]. destruct y as [|y'].
    + (* [y = 0] *) simpl in Ey. discriminate.
    + (* [y = S y'] *)
      simpl in Ey. exists y'.
      injection Ey as Ex'. apply Ex'.
Qed.

(** Unlike our proof using [bool]s, we were able to prove our fact using [Prop]s with a relatively
    straightforward approach.
    I would explain this difference by the fact that proofs of [Even] don't merely declare
    themselves to be true, but actually justify their truth with constructive evidence. We are able
    to inspect this evidence to guide how we progressed our proof. *)

(** However it was slightly annoying to have to prove [Even x'] from [Even (S (S x'))] ourselves
    when the [bool] version of evenness gave us that for free.

    We could of course wrap that logic into its own proof. Quite succinctly if we use intro patterns. *)
Theorem Even_SSx__Even_x : forall (x : nat), Even (S (S x)) -> Even x.
Proof. intros x [[|y] [= Ex]]. exists y. apply Ex. Defined.

(** [Prop] (via Fixpoint) vs [Prop] (via Inductive). *)

(** Why would we ever declare [Prop]s via [Inductive] instead of via [Fixpoint] as we did for
    [Even]? One reason is simply that something needs to be declared originally. [True], [False],
    and even [x = y] are not built into Coq as anything special; they are each declared in the
    standard library using [Inductive]. *)

(** The [Print] command can be used to view the definition of bound names. *)
Print double.
Print True.
Print False.

(** As an aside, Coqs fancy notations can make code much more concise but can sometimes obscure what
    is happening under the hood. You can use the [Print] command to peek underneath the syntax. *)
Print "x =? y". (* [x =? y] is actually calling [eqb x y]. *)
Print "x = y". (* [x = y] is actually the type [eq x y]. *)
Check eq 1 2.
Check 1 = 2.
Print "X \/ Y". (* [X \/ Y] is actually the type [or X Y]. *)
Check True \/ False.
Print "X /\ Y". (* [X /\ Y] is actually the type [and X Y]. *)
Check True /\ False.

(** The discussion doesn't end there however. Even once "enough" [Prop]s have been declared that it
    is possible to define [Prop]s via [Fixpoint] there is still reason to declare new [Prop]s via
    [Inductive]. It again comes back to how they behave in proofs. *)

(** Consider this alternative [Fixpoint] of [Even]. *)
Fixpoint Even' (x : nat) : Prop :=
match x with
| 0 => True
| S x' => match x' with
          | 0 => False
          | S x'' => (exists y, x = double y) /\ Even' x''
          end
end.

Theorem Even'_Sx__Even'_x : forall (x : nat), Even' (S x) -> ~Even' x.
Proof.
  induction x as [|x' IHx'].
  - (* [x = 0] *)
    (* Now our proof of [Even' 1] is directly a contradiction. *)
    simpl. intro contra. destruct contra.
  - (* [x = S x'] *)
    intros HEven' HSx'. apply IHx'. { apply HSx'. }
    (* As before we will destruct [Even' (S (S x'))] to try and derive [Even' x'],
       but now [Even' x'] will be given to us "for free". *)
    simpl in HEven'. destruct HEven' as [Hy Hx']. apply Hx'.
Qed.

Theorem Even'_SSx__Even'_x : forall (x : nat), Even' (S (S x)) -> Even' x.
Proof. intros x [Ey Ex]. apply Ex. Defined.

(** It seems this [Fixpoint] definition gives us the best of both worlds. We can destruct it to get
    evidence for its truth, *and* it gives us proofs for smaller arguments "for free".

    But of course nothing is really free. What we've actually done is pushed the obligation of
    proving [Even' x'] in addition to [Even' (S (S x'))] onto the user of our proof, and the same
    is true for all predecessors of [x'] too. *)

(** We can try to address this by providing [Theorems] to help building up proofs.

    This attempt will actually reveals some other pitfalls of our [Fixpoint] definition. *)
Theorem Even'_SS : forall (x : nat), Even' x -> Even' (S (S x)).
Proof.
  (* intros x HEven. destruct HEven as [Hy Hx]. *)

  (** This [destruct] does not work. The error claims that its because [Even' x] is not an inductive
      definition. What this means is that Coq can't be sure what the constructors of [Even' x] are.

      While [Even' x] is a [Prop], it is not clear which *concrete* [Prop] it is until we know more
      about [x]. This nicely brings us back around to the issues we originally observed when
      dealing with variables of type [Prop] and, as discussed then, the way out is to use the
      hypothesise we are given to learn more about [Even' x]. *)

  intros [|[|x']] HEven.
  - (* [x = 0] *)
    simpl. split. { exists 1. reflexivity. } apply HEven.
  - (* [x = 1] *)
    simpl in HEven. destruct HEven.
  - (* [x = S (S x)] *)
    case HEven. intros [y Ey] Hx. split.
    { exists (S y). simpl. f_equal. f_equal. apply Ey. } apply HEven.
Defined.

(** For comparison we provide the same "constructor" for [even] and [Even]. *)

Theorem even_SS : forall (x : nat), even x = even (S (S x)).
Proof. reflexivity. Defined.

Theorem Even_SS : forall (x : nat), Even x -> Even (S (S x)).
Proof. intros x [y Ey]. exists (S y). simpl. f_equal. f_equal. apply Ey. Defined.

(** The cracks in our [Even'] fixpoint are beginning to show. While it is more informative when we
    [destruct] it, it obliges us to perform a lot more work when creating the values in the first
    place. *)

(** [Inductive] definitions of [Prop]s can get us out of this rut. *)
Inductive ev : nat -> Prop :=
| ev_0 : ev 0
| ev_SS (x : nat) : ev x -> ev (S (S x)).

(** Here the [ev_SS] is an *actual* constructor for the type provided by Coq. Additionally where
    the [Even' x] requires us to destruct [x] before our proof that it is even, [ev x] has no such
    issues.
    Combining this with the [inversion] tactic introduced in "IndProp.v" can greatly simplify the
    amount of work in our proofs. *)

Theorem ev_Sx__ev_x : forall (x : nat), ev (S x) -> ~ev x.
Proof.
  intros x Hev.
  induction x as [|x' IHx'].
  - (* [x = 0] *)
    inversion Hev.
  - (* [x = S x'] *)
    intros HSx'. apply IHx'. { apply HSx'. } inversion Hev as [|x'2 Hx' Ex']. apply Hx'.
Qed.

Theorem ev_SSx__ev_x : forall (x : nat), ev (S (S x)) -> ev x.
Proof. intros x Hev. inversion Hev as [|x' Hx' Ex]. apply Hx'. Defined.

(** As we've hopefully learned by now however, everything is a trade-off.
    * We are still obligated to do more work when constructing a proof of [ev x] than [even x = true].
    * We are not given a [y] such that it is half of [x] as we are by [Even x].

    A summar`booy of how [even], [Even], [Even'] and [ev] compare with one another:.
    * [even x = true] will always be the easiest to prove since it asks the least of us, the
      trade-off is that it is the least informative as a hypothesis, requiring a lot of work to
      prove anything about other numbers.
    * [Even x] provides a nice middle ground, providing evidence for [x] being even but
      being somewhat frustrating to turn into proofs for other numbers.
    * [Even' x] provides lots of evidence but can be both difficult to construct and destruct in proofs.
    * [ev x] provides just as many obligations of [Even' x] to prove, but those obligations are
      much easier to satisfy. It similarly provides much evidence when given as a hypothesis but
      without the pitfalls of trying to destruct an [Even' x]. *)

(** A final point regarding the different means of defining of properties.

    Where [bool] tests must always be decidable properties, [Prop]s are able to represent
    undecidable properties as well. But there is a further distinction that can be made between
    [Prop]s defined using [Definition] or [Fixpoint], and [Prop]s defined using [Inductive].
    [Prop]s definable by [Fixpoint] must be properties which are *computable* by recursion on the
    arguments to the [Fixpoint]. I won't give detailed examples here because later chapters will
    explore this in more depth but at the beginning of the "IndProp.v" chapter the example of the
    "Collatz Conjecture" is given as a property of [nat]s which cannot be defined as a
    [Fixpoint] test or [Prop], only as an [Inductive] [Prop]. *)


Definition collatz_next (n : nat) : nat :=
  if Nat.even n then Nat.div n 2 else 3 * n + 1.

(* Function to compute the nth iteration of the Collatz sequence *)
Fixpoint collatz_iterate (n : nat) (steps : nat) : nat :=
  match steps with
  | 0 => n
  | S p => collatz_iterate (collatz_next n) p
  end.

(* The Collatz conjecture as a non-inductive Prop *)
Definition collatz_conjecture : Prop :=
  forall n : nat, n > 0 -> exists k : nat, collatz_iterate n k = 1.