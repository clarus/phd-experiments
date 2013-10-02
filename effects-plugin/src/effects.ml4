module Effect = struct
  type t = {
    path : Names.module_path;
    name : Names.Id.t;
    typ : Constr.constr }
  
  let of_syntax (name : Names.Id.t) (typ : Constrexpr.constr_expr) : t = {
    path = Lib.current_mp ();
    name = name;
    typ = Constrintern.interp_constr Evd.empty (Global.env ()) typ }
end

(** Syntax extension do add an "Effect" command. *)
VERNAC COMMAND EXTEND Effect CLASSIFIED AS QUERY
| [ "Effect" ident(name) constr(typ) ] -> [
  Effect.of_syntax name typ;
  failwith (Names.Id.to_string name) ]
END
