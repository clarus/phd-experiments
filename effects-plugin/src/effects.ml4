(** Syntax extension do add an "Effect" command. *)
VERNAC COMMAND EXTEND Extraction CLASSIFIED AS QUERY
| [ "Effect" global(x) ] -> [ failwith (Libnames.string_of_reference x) ]
END
