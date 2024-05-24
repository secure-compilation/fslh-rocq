From QuickChick Require Import QuickChick.

Inductive mynat : Type :=
  | OO
  | S1 (n : mynat)
  | S2 (n : mynat)
  | S3 (n : mynat).

Derive (Arbitrary, Shrink, Show) for mynat.

(* Time Elapsed: 0.100883s  *)
QuickChick (forAll arbitrary (fun (n:mynat) =>
            true)).

(* Time Elapsed: 5.507796s -- with discards *)
QuickChick (forAll arbitrary (fun (n:mynat) =>
            (implication false false))).

Fixpoint size_mynat (n:mynat) : nat :=
  match n with
  | OO => 1
  | S1 n' | S2 n' | S3 n' => 1 + size_mynat n'
  end.

QuickChick (forAll arbitrary (fun (n:mynat) =>
            collect (size_mynat n) true)).
