From QuickChick Require Import QuickChick. Import QcNotation.

Inductive mynat : Type :=
  | OO
  | S1 (n : mynat)
  | S2 (n : mynat)
  | S3 (n : mynat).

(* Derive (Arbitrary, Show) for mynat.
-- Wrote down these instances explicitly below, but it doesn't change much. *)

Instance GenSizedmynat : GenSized mynat :=
{|
  arbitrarySized := fun s : nat =>
    (let fix arb_aux (size : nat) : G mynat :=
       match size with
       | 0 => returnGen OO
       | S size' =>
           freq [(1, returnGen OO);
                 (1, bindGen (arb_aux size') (fun p0 : mynat => returnGen (S1 p0)));
                 (1, bindGen (arb_aux size') (fun p0 : mynat => returnGen (S2 p0)));
                 (1, bindGen (arb_aux size') (fun p0 : mynat => returnGen (S3 p0)))]
                 (* Using liftM here doubles the time with discards *)
       end in
     arb_aux) s
|}.

(* This one doesn't seem to impact performance *)
Instance Showmynat : Show mynat :=
{|
  show := fun x : mynat =>
    let fix aux (x' : mynat) : string :=
        match x' with
        | OO => "OO"%string
        | S1 p0 => ("S1 " ++ smart_paren (aux p0))%string
        | S2 p0 => ("S2 " ++ smart_paren (aux p0))%string
        | S3 p0 => ("S3 " ++ smart_paren (aux p0))%string
        end in
    aux x
|}.

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
