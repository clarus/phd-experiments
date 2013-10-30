open Constr

module Effect = struct
  open Libobject
  
  (** An effect is a name and a type to encode it. *)
  (* FIXME: add a module path. *)
  type t = {
    name : Names.Id.t;
    typ : constr }
  
  (** Create an effect from an user entry. *)
  let of_syntax (name : Names.Id.t) (typ : Constrexpr.constr_expr) : t = {
    name = name;
    typ =
      let env = Global.env () in
      let typ = Constrintern.interp_constr Evd.empty env typ in
      match kind (Typing.type_of env Evd.empty typ) with
      | Sort _ -> typ
      | _ -> Errors.error "excepted a type to describe the effect" }
  
  (** Internal table to store the list of effects. *)
  module Table = struct
    open Names
    open Pp
    
    (** We store effects using a global map reference. The summary system
        handles the backtracking. *)
    let _table : Constr.constr Id.Map.t ref =
      Summary.ref "effects" Id.Map.empty
    
    (** Register a new effect (must have a new name). *)
    let add (e : t) : unit =
      if Id.Map.mem e.name !_table then
        Errors.alreadydeclared (Id.print e.name ++ str " already exists")
      else
        _table := Id.Map.add e.name e.typ !_table
    
    (*(** Remove an existing effect (must be existing). *)
    let remove (e : t) : unit =
      if Id.Map.mem e.name !_table then
        _table := Id.Map.remove e.name !_table
      else
        Errors.anomaly (Id.print e.name ++ str " not declared")*)
  end
  
  (** Convert an effect to an object for the gobal state. *)
  let to_object : t -> obj =
    declare_object { default_object "Effect" with
      cache_function = (fun (_, e) -> Table.add e);
      (*classify_function = (fun _ -> Dispose);
      discharge_function = (fun (_, e) -> Table.remove e; None)*) }
end

(** Syntax extension to add an "Effect" command to register a new effect. *)
VERNAC COMMAND EXTEND Effect CLASSIFIED AS SIDEFF
| [ "Effect" ident(name) constr(typ) ] -> [ Lib.add_anonymous_leaf (Effect.to_object (Effect.of_syntax name typ)) ]
END

(*(** Syntax extension to add an "EDefinition" command to define a new expression with effects. *)
VERNAC COMMAND EXTEND EDefinition CLASSIFIED AS SIDEFF
| [ "EDefinition" ident(name) constr(value) ] -> [ () ]
END*)
