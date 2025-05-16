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

(* Wrote down Arbitrary instance explicitly below, but now with thunks outside and liftM *)

Instance GenSizedmynat : GenSized mynat2 :=
{|
  arbitrarySized := fun s : nat =>
    (let fix arb_aux (size : nat) : G mynat2 :=
       match size with
       | 0 => returnGen OO
       | S size' =>
           freq [(1, thunkGen (fun _ => returnGen OO));
                 (1, thunkGen (fun _ => liftM S1 (arb_aux size')));
                 (1, thunkGen (fun _ => liftM S2 (arb_aux size')));
                 (1, thunkGen (fun _ => liftM S3 (arb_aux size')));
                 (1, thunkGen (fun _ => liftM S4 (arb_aux size')));
                 (1, thunkGen (fun _ => liftM S5 (arb_aux size')));
                 (1, thunkGen (fun _ => liftM S6 (arb_aux size')))]
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
