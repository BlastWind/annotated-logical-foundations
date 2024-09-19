(* From extract chapter of verified functional algorithms *)
(* https://softwarefoundations.cis.upenn.edu/vfa-current/Extract.html *)
Require Coq.extraction.Extraction.
Extraction Language OCaml.

Fixpoint double (n:nat) :=
  match n with
  | O => O
  | S n' => S (S (double n'))
  end.

Extract Inductive bool => "bool" [ "true" "false" ].

Extract Inductive nat => "int"
  [ "0" "(fun x -> x + 1)" ]
  "(fun zero succ n -> if n=0 then zero () else succ (n-1))".