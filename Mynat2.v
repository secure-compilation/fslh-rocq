From QuickChick Require Import QuickChick.

Inductive mynat2 : Type :=
  | OO
  | S1 (n : mynat2)
  | S2 (n : mynat2)
  | S3 (n : mynat2)
  | S4 (n : mynat2)
  | S5 (n : mynat2)
  | S6 (n : mynat2).

Derive (Arbitrary, Shrink, Show) for mynat2.

(* Time Elapsed: 24.980577s *)
QuickChick (forAll arbitrary (fun (n:mynat2) =>
            true)).

(* Time Elapsed: 2824.795694s -- with discards *)
QuickChick (forAll arbitrary (fun (n:mynat2) =>
            (implication false false))).

Fixpoint size_mynat2 (n:mynat2) : nat :=
  match n with
  | OO => 1
  | S1 n' | S2 n' | S3 n'
  | S4 n' | S5 n' | S6 n' => 1 + size_mynat2 n'
  end.

QuickChick (forAll arbitrary (fun (n:mynat2) =>
            collect (size_mynat2 n) true)).
