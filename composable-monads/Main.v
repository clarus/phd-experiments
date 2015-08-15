(** Experiments on encoding concurrency in Coq. *)
Require Import Arith.
Require Import List.
Require Import Streams.
Require Import String.

Import ListNotations.
Local Open Scope string_scope.

Set Implicit Arguments.

Module Result.
  Inductive t (A B C : Type) : Type :=
  | Val : A -> t A B C
  | Err : B -> t A B C
  | Mon : C -> t A B C.

  Arguments Val [A] [B] [C] _.
  Arguments Err [A] [B] [C] _.
  Arguments Mon [A] [B] [C] _.
End Result.

Import Result.

(** Definition of a computation. *)
Module C.
  Inductive t (S : Type) (E : Type) (A : Type) : Type :=
  | make : (S -> Result.t A E (t S E A) * S) -> t S E A.

  Definition open S E A (x : t S E A) :=
    match x with
    | make x' => x'
    end.
End C.

(** Monadic return. *)
Definition ret {S E A} (x : A) : C.t S E A :=
  C.make (fun s => (Val x, s)).

(** Monadic bind. *)
Fixpoint bind S E A B (x : C.t S E A) (f : A -> C.t S E B) : C.t S E B :=
  C.make (fun s =>
    match C.open x s with
    | (Val x, s) => (Mon (f x), s)
    | (Err e, s) => (Err e, s)
    | (Mon x, s) => (Mon (bind x f), s)
    end).

Notation "'let!' X ':=' A 'in' B" := (bind A (fun X => B))
  (at level 200, X ident, A at level 100, B at level 200).

(** Raw evaluation. *)
Fixpoint eval S E A (x : C.t S E A) (s : S) : (A + E) * S :=
  match C.open x s with
  | (Val x, s) => (inl x, s)
  | (Err e, s) => (inr e, s)
  | (Mon x, s) => eval x s
  end.

(** Augment the state. *)
Fixpoint lift_state S1 S2 E A (x : C.t S1 E A) : @C.t (S1 * S2) E A :=
  C.make (fun (s : S1 * S2) =>
    let (s1, s2) := s in
    match C.open x s1 with
    | (Val x, s1) => (Val x, (s1, s2))
    | (Err e, s1) => (Err e, (s1, s2))
    | (Mon x, s1) => (Mon (lift_state _ x), (s1, s2))
    end).

(** Apply an isomorphism to the state. *)
Fixpoint map_state S1 S2 E A (f : S1 -> S2) (g : S2 -> S1) (x : C.t S1 E A)
  : C.t S2 E A :=
  C.make (fun (s2 : S2) =>
    let s1 := g s2 in
    let (r, s1) := C.open x s1 in
    (match r with
    | Val x => Val x
    | Err e => Err e
    | Mon x => Mon (map_state f g x)
    end, f s1)).

Module Option.
  Definition none A : C.t unit unit A :=
    C.make (fun _ => (Err tt, tt)).
End Option.

Module Error.
  Definition raise E A (e : E) : C.t unit E A :=
    C.make (fun _ => (Err e, tt)).
End Error.

Module Log.
  Definition t := list.

  Definition log A (x : A) : C.t (t A) Empty_set unit :=
    C.make (fun s => (Val tt, x :: s)).
End Log.

Module State.
  Definition read (S : Type) (_ : unit) : C.t S Empty_set S :=
    C.make (fun s => (Val s, s)).

  Definition write (S : Type) (x : S) : C.t S Empty_set unit :=
    C.make (fun _ => (Val tt, x)).
End State.

(** A source of information for a concurrent scheduler. *)
Module Entropy.
  Require Import BinNat.

  Definition t := Stream bool.

  Definition left : t := Streams.const true.

  Definition right : t := Streams.const false.

  Definition inverse (e : t) : t :=
    Streams.map negb e.

  Definition half : t :=
    let cofix aux b :=
      Streams.Cons b (aux (negb b)) in
    aux true.

  CoFixpoint random_naturals (n : N) : Stream N :=
    let n' := N.modulo (137 * n + 187) 256 in
    Streams.Cons n (random_naturals n').

  Definition random (seed : N) : t :=
    Streams.map (fun n => N.even (N.div n 64)) (random_naturals seed).

  Module Test.
    Fixpoint hds A (n : nat) (e : Stream A) : list A :=
      match n with
      | O => []
      | S n => Streams.hd e :: hds n (Streams.tl e)
      end.

    Compute hds 20 (random_naturals 0).
    Compute hds 20 (random 0).
    Compute hds 20 (random 12).
    Compute hds 20 (random 23).
  End Test.
End Entropy.

Module Concurrency.
  (** Executes [x] and [y] concurrently, using a boolean stream as source of entropy. *)
  Fixpoint par S E A B
    (x : C.t (S * Entropy.t) E A) (y : C.t (S * Entropy.t) E B) {struct x}
    : C.t (S * Entropy.t) E (A * B) :=
    let fix par_aux y {struct y} : C.t (S * Entropy.t) E (A * B) :=
      C.make (fun (s : S * Entropy.t) =>
        match s with
        | (s, Streams.Cons b bs) =>
          if b then
            let (r, ss) := C.open x (s, bs) in
            (match r with
            | Val x => Mon (let! y := y in ret (x, y))
            | Err e => Err e
            | Mon x => Mon (par x y)
            end, ss)
          else
            let (r, ss) := C.open y (s, bs) in
            (match r with
            | Val y => Mon (let! x := x in ret (x, y))
            | Err e => Err e
            | Mon y => Mon (par_aux y)
            end, ss)
        end) in
    C.make (fun (s : S * Entropy.t) =>
      match s with
      | (s, Streams.Cons b bs) =>
        if b then
          let (r, ss) := C.open x (s, bs) in
          (match r with
          | Val x => Mon (let! y := y in ret (x, y))
          | Err e => Err e
          | Mon x => Mon (par x y)
          end, ss)
        else
          let (r, ss) := C.open y (s, bs) in
          (match r with
          | Val y => Mon (let! x := x in ret (x, y))
          | Err e => Err e
          | Mon y => Mon (par_aux y)
          end, ss)
      end).

  Definition par_unit S E (x : C.t (S * Entropy.t) E unit) (y : C.t (S * Entropy.t) E unit)
    : C.t (S * Entropy.t) E unit :=
    let! _ := par x y in
    ret tt.

  (** Make [x] atomic. *)
  Fixpoint atomic S E A (x : C.t S E A) : C.t S E A :=
    C.make (fun (s : S) =>
      match C.open x s with
      | (Val _, _) as y | (Err _, _) as y => y
      | (Mon x, s) => C.open (atomic x) s
      end).
End Concurrency.

Module List.
  Fixpoint iter_seq S E A (f : A -> C.t S E unit) (l : list A) : C.t S E unit :=
    match l with
    | [] => ret tt
    | x :: l =>
      let! _ := f x in
      iter_seq f l
    end.

  Fixpoint iter_par S E A (f : A -> C.t (S * Entropy.t) E unit) (l : list A)
    : C.t (S * Entropy.t) E unit :=
    match l with
    | [] => ret tt
    | x :: l => Concurrency.par_unit (f x) (iter_par f l)
    end.
End List.

Module Event.
  Definition t := list.

  Definition loop_seq S E A (f : A -> C.t S E unit) : C.t (S * t A) E unit :=
    C.make (fun (s : S * t A) =>
      let (s, events) := s in
      (Mon (lift_state (t A) (List.iter_seq f events)), (s, []))).

  Definition loop_par S E A (f : A -> C.t (S * Entropy.t) E unit)
    : C.t (S * t A * Entropy.t) E unit :=
    C.make (fun (s : S * t A * Entropy.t) =>
      match s with
      | (s, events, entropy) =>
        let c := List.iter_par f events in
        let c := lift_state (t A) c in
        let c := map_state
          (fun ss => match ss with (s1, s2, s3) => (s1, s3, s2) end)
          (fun ss => match ss with (s1, s2, s3) => (s1, s3, s2) end)
          c in
        (Mon c, (s, [], entropy))
      end).

  Module Test.
    Definition log_all (_ : unit) : C.t (Log.t nat * t nat * Entropy.t) Empty_set unit :=
      loop_par (fun n =>
        lift_state _ (Log.log n)).

    Definition eval (inputs : list nat) (entropy : Entropy.t) : list nat :=
      match snd (eval (log_all tt) ([], inputs, entropy)) with
      | (output, _, _) => output
      end.

    Compute eval [] Entropy.left.
    Compute eval [1; 2; 3] Entropy.left.
    Compute eval [1; 2; 3] Entropy.right.
  End Test.
End Event.

Module Test.
  Definition eval_seq (x : C.t (list nat) Empty_set unit) : list nat :=
    snd (eval x []).

  Definition eval_par (x : C.t (list nat * Entropy.t) Empty_set unit) (e : Entropy.t) : list nat :=
    fst (snd (eval x ([], e))).

  (** Two threads are printing concurrently two lists of numbers. *)
  Module PrintList.
    Fixpoint print_before (n : nat) : C.t (Log.t nat) Empty_set unit :=
      match n with
      | O => ret tt
      | S n =>
        let! _ := Log.log n in
        print_before n
      end.

    Definition two_prints_seq (n : nat) : C.t (Log.t nat) Empty_set unit :=
      let! _ := print_before n in
      print_before (2 * n).

    Definition print_before_par (n : nat) : C.t (Log.t nat * Entropy.t) Empty_set unit :=
      lift_state (Entropy.t) (print_before n).

    Definition two_prints_par (n : nat) : C.t (Log.t nat * Entropy.t) Empty_set unit :=
      Concurrency.par_unit (print_before_par n) (print_before_par (2 * n)).

    Compute eval_seq (print_before 12).
    Compute eval_seq (two_prints_seq 12).

    Compute eval_par (print_before_par 12) Entropy.half.
    Compute eval_par (two_prints_par 12) Entropy.left.
    Compute eval_par (two_prints_par 12) Entropy.right.
    Compute eval_par (two_prints_par 12) Entropy.half.
    Compute eval_par (two_prints_par 12) (Entropy.random 0).
  End PrintList.

  (** A list of threads are printing a number each. *)
  Module ListOfPrints.
    Definition print_seq_seq (n k : nat) : C.t (Log.t nat) Empty_set unit :=
      List.iter_seq (Log.log (A := nat)) (List.seq n k).

    Definition print_seq_par (n k : nat) : C.t (Log.t nat * Entropy.t) Empty_set unit :=
      List.iter_par (fun n => lift_state _ (Log.log n)) (List.seq n k).

    Compute eval_seq (print_seq_seq 10 20).
    Compute eval_par (print_seq_par 10 20) Entropy.left.
    Compute eval_par (print_seq_par 10 20) Entropy.right.
    Compute eval_par (print_seq_par 10 20) (Entropy.random 12).
  End ListOfPrints.

  (** Simple manager for a list of things to do, with a UI saving data on a server. *)
  Module TodoManager.
    (** Event from the UI. *)
    Module UiInput.
      Inductive t : Set :=
      | Add : string -> t
      | Remove : nat -> t.
    End UiInput.

    (** Message to the UI. *)
    Module UiOutput.
      Inductive t :=
      | Make : list string -> t.
    End UiOutput.

    (** Event from the server. *)
    Module ServerInput.
      Inductive t :=
      | Make : list string -> t.
    End ServerInput.

    (** Message to the server. *)
    Module ServerOutput.
      Inductive t :=
      | Make : list string -> t.
    End ServerOutput.

    Module Model.
      (** The model is a list of tasks. *)
      Inductive t :=
      | Make : list string -> t.

      Definition add (task : string) : C.t Model.t Empty_set unit :=
        Concurrency.atomic (
          let! model := State.read Model.t tt in
          match model with
          | Model.Make tasks => State.write (Model.Make (task :: tasks))
          end).

      Definition remove (id : nat) : C.t Model.t Empty_set unit :=
        Concurrency.atomic (
          let! model := State.read Model.t tt in
          match model with
          | Model.Make tasks => State.write (Model.Make tasks) (* TODO *)
          end).

      Definition get (_ : unit) : C.t Model.t Empty_set Model.t :=
        State.read Model.t tt.

      Definition set (model : t) : C.t Model.t Empty_set unit :=
        State.write model.
    End Model.

    (** Send an update to the UI system. *)
    Definition push_ui (_ : unit) : C.t (Model.t * Log.t UiOutput.t) Empty_set unit :=
      let! model := lift_state (Log.t UiOutput.t) (Model.get tt) in
      match model with
      | Model.Make tasks =>
        map_state
          (fun ss => match ss with (s1, s2) => (s2, s1) end)
          (fun ss => match ss with (s1, s2) => (s2, s1) end)
          (lift_state Model.t (Log.log (UiOutput.Make tasks)))
      end.

    (** Send an update to the server. *)
    Definition push_server (_ : unit) : C.t (Model.t * Log.t ServerOutput.t) Empty_set unit :=
      let! model := lift_state (Log.t ServerOutput.t) (Model.get tt) in
      match model with
      | Model.Make tasks =>
        map_state
          (fun ss => match ss with (s1, s2) => (s2, s1) end)
          (fun ss => match ss with (s1, s2) => (s2, s1) end)
          (lift_state Model.t (Log.log (ServerOutput.Make tasks)))
      end.

    (** Update the UI and the server. *)
    Definition broadcast_model (_ : unit)
      : C.t (Model.t * Log.t UiOutput.t * Log.t ServerOutput.t * Entropy.t) Empty_set unit :=
      let c_ui := lift_state Entropy.t (lift_state (Log.t ServerOutput.t) (push_ui tt)) in
      let c_server := lift_state Entropy.t (map_state
        (fun ss => match ss with (s1, s2, s3) => (s1, s3, s2) end)
        (fun ss => match ss with (s1, s2, s3) => (s1, s3, s2) end)
        (lift_state (Log.t UiOutput.t) (push_server tt))) in
      Concurrency.par_unit c_ui c_server.

    (** Handle an event from the UI. *)
    Definition handle_ui (event : UiInput.t)
      : C.t (Model.t * Log.t UiOutput.t * Log.t ServerOutput.t * Entropy.t) Empty_set unit :=
      let lift c :=
        lift_state Entropy.t (lift_state (Log.t ServerOutput.t) (lift_state (Log.t UiOutput.t) c)) in
      match event with
      | UiInput.Add task =>
        let! _ := lift (Model.add task) in
        broadcast_model tt
      | UiInput.Remove id =>
        let! _ := lift (Model.remove id) in
        broadcast_model tt
      end.

    Definition eval_handle_ui (inputs : list UiInput.t) (entropy : Entropy.t)
      : list UiOutput.t * list ServerOutput.t :=
      match snd (eval (Event.loop_par handle_ui) (Model.Make [], [], [], inputs, entropy)) with
      | (_, ui_outputs, server_outputs, _, _) => (ui_outputs, server_outputs)
      end.

    Compute eval_handle_ui [] Entropy.left.
    Compute eval_handle_ui [UiInput.Add "task1"; UiInput.Add "task2"] Entropy.left.
    Compute eval_handle_ui [UiInput.Add "task1"; UiInput.Add "task2"] Entropy.right.

    (** Handle an event from the server. *)
    Definition handle_server (event : ServerInput.t)
      : C.t (Model.t * Log.t UiOutput.t) Empty_set unit :=
      match event with
      | ServerInput.Make tasks =>
        let! _ := lift_state (Log.t UiOutput.t) (Model.set (Model.Make tasks)) in
        push_ui tt
      end.

    Definition eval_handle_server (inputs : list ServerInput.t) (entropy : Entropy.t) : list UiOutput.t :=
      let c := Event.loop_par (fun event => lift_state Entropy.t (handle_server event)) in
      match snd (eval c (Model.Make [], [], inputs, entropy)) with
      | (_, outputs, _, _) => outputs
      end.

    Compute eval_handle_server [] Entropy.left.
    Compute eval_handle_server [ServerInput.Make ["task1"]; ServerInput.Make ["task2"]] Entropy.left.
    Compute eval_handle_server [ServerInput.Make ["task1"]; ServerInput.Make ["task2"]] Entropy.right.

    Definition lifted_handle_server (event : ServerInput.t)
      : C.t (Model.t * Log.t UiOutput.t * Log.t ServerOutput.t * Entropy.t) Empty_set unit :=
      lift_state Entropy.t (lift_state (Log.t ServerOutput.t) (handle_server event)).

    Definition State : Type :=
      (Model.t * Log.t UiOutput.t * Log.t ServerOutput.t * Event.t UiInput.t * Event.t ServerInput.t * Entropy.t)%type.

    (** The TODO manager client. *)
    Definition todo (_ : unit) : C.t State Empty_set unit :=
      let c_ui : C.t State Empty_set unit :=
        (* Handle events concurrently. *)
        let c := Event.loop_par handle_ui in
        let c := lift_state (Event.t ServerInput.t) c in
        map_state
          (fun ss => match ss with (s1, s2, s3) => (s1, s3, s2) end)
          (fun ss => match ss with (s1, s2, s3) => (s1, s3, s2) end)
          c in
      let c_server : C.t State Empty_set unit :=
        (* Handle events concurrently. *)
        let c := Event.loop_par lifted_handle_server in
        let c := lift_state (Event.t UiInput.t) c in
        map_state
          (fun ss => match ss with (s1, s2, s3, s4) => (s1, s4, s2, s3) end)
          (fun ss => match ss with (s1, s2, s3, s4) => (s1, s3, s4, s2) end)
          c in
      Concurrency.par_unit c_ui c_server.

    Definition eval (ui_inputs : list UiInput.t) (server_inputs : list ServerInput.t) (entropy : Entropy.t)
      : list UiOutput.t * list ServerOutput.t :=
      match snd (eval (todo tt) (Model.Make [], [], [], ui_inputs, server_inputs, entropy)) with
      | (_, ui_outputs, server_outputs, _, _, _) => (ui_outputs, server_outputs)
      end.

    Compute eval [] [] (Entropy.random 12).
    Compute eval [UiInput.Add "task1"] [] (Entropy.random 12).
    Compute eval [UiInput.Add "task1"; UiInput.Add "task2"] [] Entropy.left.
    Compute eval [UiInput.Add "task1"; UiInput.Add "task2"] [] Entropy.right.
    Compute eval [UiInput.Add "task1"; UiInput.Add "task2"; UiInput.Add "task3"] [] Entropy.left.
    Compute eval [UiInput.Add "task1"; UiInput.Add "task2"; UiInput.Add "task3"] [] Entropy.right.
    Compute eval [UiInput.Add "task1"; UiInput.Add "task2"; UiInput.Add "task3"] [] (Entropy.random 10).
    Compute eval [UiInput.Add "task1"; UiInput.Add "task2"] [ServerInput.Make ["task3"]] Entropy.left.
    Compute eval [UiInput.Add "task1"; UiInput.Add "task2"] [ServerInput.Make ["task3"]] Entropy.right.
    Compute eval [UiInput.Add "task1"; UiInput.Add "task2"] [ServerInput.Make ["task3"]] (Entropy.random 10).
  End TodoManager.
End Test.
