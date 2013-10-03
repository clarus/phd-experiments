open Constr

module Effect = struct
  open Libobject
  
  type t = {
(*    path : Names.ModPath.t;*)
    name : Names.Id.t;
    typ : constr }
  
  let of_syntax (name : Names.Id.t) (typ : Constrexpr.constr_expr) : t = {
(*    path = Lib.current_mp ();*)
    name = name;
    typ = Constrintern.interp_constr Evd.empty (Global.env ()) typ }
  
  module Table = struct
    open Names
    open Pp
    
    let _table : (Id.t, constr) Hashtbl.t = Hashtbl.create 17
    
    let add (e : t) : unit =
      if Hashtbl.mem _table e.name then
        Errors.alreadydeclared (Id.print e.name ++ str " already exists")
      else
        Hashtbl.add _table e.name e.typ
  end
  
  let to_object : t -> obj =
    declare_object { default_object "Effect" with
      cache_function = fun (_, e) -> Table.add e }
end

(** Syntax extension do add an "Effect" command. *)
VERNAC COMMAND EXTEND Effect CLASSIFIED AS QUERY
| [ "Effect" ident(name) constr(typ) ] -> [
  Lib.add_anonymous_leaf (Effect.to_object (Effect.of_syntax name typ));
  (*failwith (Names.Id.to_string name)*)
  () ]
END
