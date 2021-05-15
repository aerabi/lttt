From QuickChick Require Import QuickChick.
Import GenLow GenHigh.
Import QcDefaultNotation. Open Scope qc_scope.

Require Import List ZArith.
Import ListNotations.

Require Import Base.
Require Import BaseShow.

(* 𝔗 *)
Fixpoint gen_𝔗 (size : nat) : G 𝔗 :=
  match size with 
  | O => elems [ Unit ; Void ]
  | S size' => oneOf 
      [ liftGen2 𝔗mult (gen_𝔗 size') (gen_𝔗 size') ; 
        liftGen2 𝔗plus (gen_𝔗 size') (gen_𝔗 size') ;
        liftGen2 𝔗impl (gen_𝔗 size') (gen_𝔗 size') ]
  end.

Sample (gen_𝔗 0).
Sample (gen_𝔗 1).
Sample (gen_𝔗  2).

Instance gen_𝔗_sized : GenSized 𝔗 :=
  {| arbitrarySized n := gen_𝔗 n |}.

(* 𝔄 *)
Fixpoint gen_𝔄 (size : nat) : G 𝔄 :=
  match size with 
  | O => elems [ 𝔄0 ; 𝔄1 ]
  | S size' => oneOf 
      [ liftGen2 𝔄mult (gen_𝔄 size') (gen_𝔄 size') ; 
        liftGen2 𝔄plus (gen_𝔄 size') (gen_𝔄 size') ;
        liftGen2 𝔄impl (gen_𝔄 size') (gen_𝔄 size') ;
        liftGen 𝔄diam (gen_𝔄 size') ]
  end.

Sample (gen_𝔄 0).
Sample (gen_𝔄 1).
Sample (gen_𝔄  2).

Instance gen_𝔄_sized : GenSized 𝔄 :=
  {| arbitrarySized n := gen_𝔄 n |}.

(* 𝔱 *)
Fixpoint gen_𝔱 (size : nat) : G 𝔱 :=
  match size with 
  | O => elems [ 𝔱id (𝔵id 0) ; 𝔱hole ]
  | S size' => oneOf 
      [ liftGen 𝔱holecase (gen_𝔱 size') ; 
        liftGen2 𝔱pair (gen_𝔱 size') (gen_𝔱 size') ;
        liftGen2 𝔱lambda (returnGen (𝔵id 0)) (gen_𝔱 size') ]
  end.

Sample (gen_𝔱 0).
Sample (gen_𝔱 1).
Sample (gen_𝔱 2).

Instance gen_𝔱_sized : GenSized 𝔱 :=
  {| arbitrarySized n := gen_𝔱 n |}.

(* 𝔢 *)
Fixpoint gen_𝔢 (size : nat) : G 𝔢 :=
  match size with 
  | O => elems [ 𝔢id (𝔵id 0) ; 𝔢hole ]
  | S size' => oneOf 
      [ liftGen 𝔢holecase (gen_𝔢 size') ; 
        liftGen2 𝔢pair (gen_𝔢 size') (gen_𝔢 size') ;
        liftGen2 𝔢lambda (returnGen (𝔵id 0)) (gen_𝔢 size') ]
  end.

Sample (gen_𝔢 0).
Sample (gen_𝔢 1).
Sample (gen_𝔢 2).

Instance gen_𝔢_sized : GenSized 𝔢 :=
  {| arbitrarySized n := gen_𝔢 n |}.
