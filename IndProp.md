## IndProp notes

#### Inductive Hypotheses 
I had a false belief that induction on inductive props did a lot more. But turns out, it's no different from standard induction. When you induct on `A` (**no matter if you are inducting a full inductive hypothesis `A`, or some variable in `A`**) for state `A -> B -> C` — you get to assume `B -> C`, and then you have to prove the next incremental version, i.e., `S B -> S C`.

For example, given
```
Goal 1

X : Set
test : X -> bool
l, l1, l2 : list X

(1/1) -------
merge l1 l2 l ->
All (fun n : X => test n = true) l1 -> 
All (fun n : X => test n = false) l2 ->
filter test l = l1
```
Question: What would the third case generated from `induction [merge l1 l2 l]` be?
Recall that the third case of the inductive proposition `merge` is: `merge_r (x:X) (l1: list X) (l2: list X) (l: list X) (H: merge l1 l2 l): merge (l1) (x :: l2) (x :: l)`.

Answer: Our state is some `A -> B -> C -> D`, so we get to assume `B -> C -> D`, and we ought to prove `S B -> S C -> S D`:
```
Goal 3
(* abbreviated *)
IHmerge : All (fun n: X => test n = true) l1 -> All (fun n : X => test n = false) -> filter test l = l1

(3/3) --------
filter test (x :: l) = l1
```

Note, the incremental version 
Note that `l1` didn't change, but `l` and `l2` became `(x :: l)` and `(x :: l2)`. Look at the definition of `merge_r` to confirm this.