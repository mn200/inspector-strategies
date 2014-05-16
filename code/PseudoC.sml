(* PseudoC representation for inspectors and executors
 *     and a C code generator
 *)

(* Starting from hol/PseudoCScript.sml commit 41b8290
 *
 *     differences
 *         -only need scalar values in expressions, so no Array (value list)
 *         -don't need Error value because not interpreting
 *         -need deep embedding for operations for code generation
 *         -don't need to carry around memory in SeqStmt like in Seq because
 *          not interpreting
 *         -don't need Par, Abort, or Done because not interpreting
 *         -need 
 *)

datatype value =
         Int of int
         | Real of real
         | Bool of bool


datatype expr =
         (* scalar variable read *)
         VarExp of string

         (* array read, e.g., f(i) *)
         | ARead of string* expr

         (* constant value *)
         | Value of value

         (* operations needed so far for wavebench example *)
         | Max of expr * expr
         | Plus of expr * expr
         | Minus of expr * expr
         | Mult of expr * expr
         | Divide of expr * expr
         | Exp of expr      (* exponent function *)
         | Convert of expr  (* convert an integer to a double *)

         (* comparison operations *)
         | CmpGTE of expr * expr


datatype domain =
         D1D of expr * expr


(* Statements in PseudoC *)
datatype stmt =
         (* Array element definition *)
         Assign of string * expr           (* write: array and index expr *)
                   * expr                  (* rhs *)

         (* Assignment to scalar *)
         | AssignVar of string * expr      (* var = rhs *)

         (* If-the-else statement *)
         | IfStmt of expr * stmt * stmt

         (* Aname, size expression, initval *)
         (* initval is not an expression so can easily get type info *)
         | Malloc of string * expr * value

         (* for ( lb <= i < ub ) body *)
         (* one string for one iterator *)
         | ForLoop of string * domain * stmt

         (* iterations of loop can be executed concurrently *)
         (* for ( lb <= i < ub ) body *)
         | ParForLoop of string * domain * stmt

         (* Statement sequencing.  *)
         (* Named different than Seq because somewhat different. *)
         | SeqStmt of stmt list


(**** Code Generator from PseudoC to C ****)

fun genCexpr ast =
    case ast of
        VarExp(id) => id

      | ARead(id,idx) => id^"["^(genCexpr idx)^"]"

      | Value(Int(n)) => Int.toString(n)
      | Value(Real(n)) => Real.toString(n)

      | Max(e1,e2) => "MAX("^(genCexpr e1)^","^(genCexpr e2)

      | Plus(e1,e2) => "("^(genCexpr e1)^")+("^(genCexpr e2)^")"
      | Minus(e1,e2) => "("^(genCexpr e1)^")-("^(genCexpr e2)^")"
      | Mult(e1,e2) => "("^(genCexpr e1)^")*("^(genCexpr e2)^")"
      | Divide(e1,e2) => "("^(genCexpr e1)^")/("^(genCexpr e2)^")"
      | Exp(e1) => "exp("^(genCexpr e1)^")"
      | Convert(e1) => "(double)("^(genCexpr e1)^")"

      | CmpGTE(e1,e2) => "("^(genCexpr e1)^")>=("^(genCexpr e2)^")"

(* lvl specifies the current tab level, should usually start at 0 *)
fun genCstmt ast lvl =
    (* 4 spaces of indentation per level *)
    let fun indent lvl = if lvl>0 then "    "^(indent (lvl-1)) else ""
    in
        case ast of
            Assign(id,idx,rhs) =>
            (indent lvl) ^ id^"["^(genCexpr idx)^"] = "^(genCexpr rhs)^";\n"

          | AssignVar(var,rhs) =>
            (indent lvl) ^ var^" = "^(genCexpr rhs)^";\n"

          | IfStmt(e,thenbody,elsebody) =>
            (indent lvl) ^"if ("^(genCexpr e)^") {\n"
            ^(genCstmt thenbody (lvl+1))
            ^(genCstmt elsebody (lvl+1))
            ^(indent lvl)^"}\n"

          (* FIXME: output init code *)                               
          | Malloc(id,sz,Int(n)) =>
            (indent lvl) ^ id^" = (int*)malloc(sizeof(int)*"
            ^(genCexpr sz)
            ^");\n"

          | ForLoop(iter,D1D(lb,ub),body) =>
            (indent lvl) ^"for (int "^iter^"=("^(genCexpr lb)^"); "
            ^iter^"<("^(genCexpr ub)^"); "^iter^"++) {\n"
            ^(genCstmt body (lvl+1))
            ^(indent lvl) ^"}\n"

          | ParForLoop(iter,D1D(lb,ub),body) =>
            (indent lvl) ^"#pragma omp parallel for\n"
            ^(indent lvl) ^"for (int "^iter^"=("^(genCexpr lb)^"); "
            ^iter^"<("^(genCexpr ub)^"); "^iter^"++) {\n"
            ^(genCstmt body (lvl+1))
            ^(indent lvl) ^"}\n"

         | SeqStmt(s::slist) =>
           (genCstmt s lvl)^(genCstmt (SeqStmt(slist)) lvl)

         | SeqStmt([]) => "" 

    end
