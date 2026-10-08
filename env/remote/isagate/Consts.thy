theory Consts
  imports ExecSpec.API_H ExecSpec.ArchIntermediate_H
begin

text \<open>Dump every constant defined in l4v's executable spec (session ExecSpec, including the machine
theories it loads): name, defining theory, type. Output: GATE_OUT/consts.tsv\<close>

ML \<open>
  val out = Path.explode (getenv "GATE_OUT") + Path.basic "consts.tsv"
  val ctxt = Config.put show_question_marks false @{context}
  val consts = Sign.consts_of @{theory}
  val space = Consts.space_of consts
  val {constants, ...} = Consts.dest consts
  fun row (name, (ty, _)) =
    let val thy = #theory_long_name (Name_Space.the_entry space name)
    in if String.isPrefix "ExecSpec." thy
       then SOME (name ^ "\t" ^ thy ^ "\t" ^
                  (Print_Mode.setmp [] (fn () => Syntax.string_of_typ ctxt ty) ()
                   |> String.translate (fn #"\n" => " " | c => str c)))
       else NONE
    end
  val rows = map_filter row constants
  val _ = File.write out (cat_lines rows ^ "\n")
  val _ = writeln ("GATE consts: " ^ string_of_int (length rows))
\<close>

end
