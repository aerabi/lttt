(* Event-based language [1, appendix A] *)

Inductive 𝔗 : Type :=
  | Unit : 𝔗
  | Void : 𝔗
  | 𝔗mult : 𝔗 -> 𝔗 -> 𝔗
  | 𝔗plus : 𝔗 -> 𝔗 -> 𝔗
  | 𝔗impl : 𝔗 -> 𝔗 -> 𝔗
  | 𝔗ceil : 𝔗 -> 𝔗.

Notation "T × T'" := (𝔗mult T T') (at level 20, left associativity).
Notation "T + T'" := (𝔗plus T T') (at level 50, left associativity).
Notation "T → T'" := (𝔗impl T T') (at level 40, left associativity).
Notation "⌈ T ⌉" := (𝔗ceil T) (at level 30, left associativity).

Inductive 𝔄 : Type :=
  | 𝔄1 : 𝔄
  | 𝔄0 : 𝔄
  | 𝔄mult : 𝔄 -> 𝔄 -> 𝔄
  | 𝔄plus : 𝔄 -> 𝔄 -> 𝔄
  | 𝔄impl : 𝔄 -> 𝔄 -> 𝔄
  | 𝔄flor : 𝔄 -> 𝔄
  | 𝔄diam : 𝔄 -> 𝔄.

Notation "A ⊗ A'" := (𝔄mult A A') (at level 20, left associativity).
Notation "A ⊕ A'" := (𝔄plus A A') (at level 50, left associativity).
Notation "A ⊸ A'" := (𝔄impl A A') (at level 40, left associativity).
Notation "⌊ A ⌋" := (𝔄flor A) (at level 30, left associativity).
Notation "◇ A" := (𝔄diam A) (at level 25, left associativity).

Inductive 𝔵 : Type :=
  | 𝔵id : nat -> 𝔵.

Inductive 𝔱 : Type :=
  | 𝔱id : 𝔵 -> 𝔱
  | 𝔱hole : 𝔱
  | 𝔱holecase : 𝔱 -> 𝔱
  | 𝔱pair : 𝔱 -> 𝔱 -> 𝔱
  | 𝔱prj : nat -> 𝔱 -> 𝔱
  | 𝔱inj : nat -> 𝔱 -> 𝔱
  | 𝔱case : 𝔱 -> 𝔵 -> 𝔱 -> 𝔵 -> 𝔱 -> 𝔱
  | 𝔱lambda : 𝔵 -> 𝔱 -> 𝔱
  | 𝔱app : 𝔱 -> 𝔱 -> 𝔱
  | 𝔱suspend : 𝔢 -> 𝔱
with 𝔢 : Type :=
  | 𝔢id : 𝔵 -> 𝔢
  | 𝔢hole : 𝔢
  | 𝔢holecase : 𝔢 -> 𝔢
  | 𝔢holelet : 𝔢 -> 𝔢 -> 𝔢
  | 𝔢pair : 𝔢 -> 𝔢 -> 𝔢
  | 𝔢let : 𝔵 -> 𝔵 -> 𝔢 -> 𝔢 -> 𝔢
  | 𝔢inj : nat -> 𝔢 -> 𝔢
  | 𝔢case : 𝔢 -> 𝔵 -> 𝔢 -> 𝔵 -> 𝔢 -> 𝔢
  | 𝔢lambda : 𝔵 -> 𝔢 -> 𝔢
  | 𝔢app : 𝔢 -> 𝔢 -> 𝔢
  | 𝔢return : 𝔢 -> 𝔢
  | 𝔢bind : 𝔵 -> 𝔢 -> 𝔢 -> 𝔢
  | 𝔢force : 𝔱 -> 𝔢
  | 𝔢flor : 𝔱 -> 𝔢
  | 𝔢florlet : 𝔵 -> 𝔢 -> 𝔢 -> 𝔢.
