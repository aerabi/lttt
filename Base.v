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

Inductive 𝓐 : Type :=
  | 𝓐1 : 𝓐
  | 𝓐0 : 𝓐
  | 𝓐mult : 𝓐 -> 𝓐 -> 𝓐
  | 𝓐plus : 𝓐 -> 𝓐 -> 𝓐
  | 𝓐impl : 𝓐 -> 𝓐 -> 𝓐
  | 𝓐flor : 𝓐 -> 𝓐
  | 𝓐diam : 𝓐 -> 𝓐.

Notation "A ⊗ A'" := (𝓐mult A A') (at level 20, left associativity).
Notation "A ⊕ A'" := (𝓐plus A A') (at level 50, left associativity).
Notation "A ⊸ A'" := (𝓐impl A A') (at level 40, left associativity).
Notation "⌊ A ⌋" := (𝓐flor A) (at level 30, left associativity).
Notation "◇ A" := (𝓐diam A) (at level 25, left associativity).