From QuickChick Require Import QuickChick.
Import GenLow GenHigh.
Import QcDefaultNotation. Open Scope qc_scope.

Require Import List ZArith.
Import ListNotations.

Require Import Base.
Require Import BaseShow.

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