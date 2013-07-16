Module BlockId.
  Definition t := nat.
End BlockId.

Module Field.
  Inductive t : Set :=
  | array (i : nat)
  | struct (f : nat)
  | union (f : nat).
End Field.

Module Path.
  Definition t := list Field.t.
End Path.

Module Value.
  Inductive t : Set :=
(*   | bits (bs : list bool) *)
  | bits (bs : nat) (* for now, simply [nat] *)
  | array (vs : list t)
  | struct (fields : list t)
  | union (field : nat) (v : t)
  | pointer (bl : BlockId.t) (p : Path.t).
End Value.

Module Memory.
  Definition t := list Value.t.
End Memory.