From QuickChick Require Import QuickChick. Import QcNotation.

Inductive mynat2 : Type :=
  | OO
  | S1 (n : mynat2)
  | S2 (n : mynat2)
  | S3 (n : mynat2)
  | S4 (n : mynat2)
  | S5 (n : mynat2)
  | S6 (n : mynat2).

Derive (Show) for mynat2.

(* Wrote down Arbitrary instance explicitly below, but now with thunks outside *)

Instance GenSizedmynat : GenSized mynat2 :=
{|
  arbitrarySized := fun s : nat =>
    (let fix arb_aux (size : nat) : G mynat2 :=
       match size with
       | 0 => returnGen OO
       | S size' =>
           freq [(1, thunkGen (fun _ => returnGen OO));
                 (1, thunkGen (fun _ => bindGen (arb_aux size') (fun p0 => returnGen (S1 p0))));
                 (1, thunkGen (fun _ => bindGen (arb_aux size') (fun p0 => returnGen (S2 p0))));
                 (1, thunkGen (fun _ => bindGen (arb_aux size') (fun p0 => returnGen (S3 p0))));
                 (1, thunkGen (fun _ => bindGen (arb_aux size') (fun p0 => returnGen (S4 p0))));
                 (1, thunkGen (fun _ => bindGen (arb_aux size') (fun p0 => returnGen (S5 p0))));
                 (1, thunkGen (fun _ => bindGen (arb_aux size') (fun p0 => returnGen (S6 p0))))]
       end in
     arb_aux) s
|}.

(* Time Elapsed: 24.980577s -- without thunks *)
(* Time Elapsed: 0.025391s -- with thunks *)
QuickChick (forAll arbitrary (fun (n:mynat2) =>
            true)).

(* Time Elapsed: 2824.795694s -- with discards, without thunks *)
(* Time Elapsed: 0.090265s -- with discards, with thunks *)
QuickChick (forAll arbitrary (fun (n:mynat2) =>
            (implication false false))).
