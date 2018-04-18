structure tigertrans :> tigertrans = struct

open tigerframe
open tigertree
open tigertemp
open tigerabs

exception breakexc
exception divCero
	
type level = {parent:frame option , frame: frame, level: int}
(*datatype access = InFrame of int | InReg of tigertemp.label*)
type access = tigerframe.access

type frag = tigerframe.frag
val fraglist = ref ([]: frag list)

val actualLevel = ref ~1 (* _tigermain debe tener level = 0. *)
fun getActualLev() = !actualLevel

val outermost: level = {parent=NONE,
	frame=newFrame{name="_tigermain", formals=[]}, level=getActualLev()}
fun newLevel{parent={parent, frame, level}, name, formals} =
	{
	parent=SOME frame,
	frame=newFrame{name=name, formals=formals},
	level=level+1}
fun allocArg{parent, frame, level} b = tigerframe.allocArg frame b
fun allocLocal{parent, frame, level} b = tigerframe.allocLocal frame b
fun formals{parent, frame, level} = tigerframe.formals frame

datatype exp =
	Ex of tigertree.exp
	| Nx of tigertree.stm
	| Cx of label * label -> tigertree.stm

fun seq [] = EXP (CONST 0)
	| seq [s] = s
	| seq (x::xs) = SEQ (x, seq xs)

fun unEx (Ex e) = e
	| unEx (Nx s) = ESEQ(s, CONST 0)
	| unEx (Cx cf) =
	let
		val r = newtemp()
		val t = newlabel()
		val f = newlabel()
	in
		ESEQ(seq [MOVE(TEMP r, CONST 1),
			cf (t, f),
			LABEL f,
			MOVE(TEMP r, CONST 0),
			LABEL t],
			TEMP r)
	end

fun unNx (Ex e) = EXP e
	| unNx (Nx s) = s
	| unNx (Cx cf) =
	let
		val t = newlabel()
		val f = newlabel()
	in
		seq [cf(t,f),
			LABEL t,
			LABEL f]
	end

fun unCx (Nx s) = raise Fail ("Error (UnCx(Nx..))")
	| unCx (Cx cf) = cf
	| unCx (Ex (CONST 0)) =
	(fn (t,f) => JUMP(NAME f, [f]))
	| unCx (Ex (CONST _)) =
	(fn (t,f) => JUMP(NAME t, [t]))
	| unCx (Ex e) =
	(fn (t,f) => CJUMP(NE, e, CONST 0, t, f))

fun Ir(e) =
	let	fun aux(Ex e) = tigerit.tree(EXP e)
		| aux(Nx s) = tigerit.tree(s)
		| aux _ = raise Fail "bueno, a completar!"
		fun aux2(PROC{body, frame}) = aux(Nx body)
		| aux2(STRING(l, "")) = l^":\n"
		| aux2(STRING("", s)) = "\t"^s^"\n"
		| aux2(STRING(l, s)) = l^":\t"^s^"\n"
		fun aux3 [] = ""
		| aux3(h::t) = (aux2 h)^(aux3 t)
	in	aux3 e end
fun nombreFrame frame = print(".globl " ^ tigerframe.name frame ^ "\n")

(* While y for necesitan la u'ltima etiqueta para un break *)
local
	val salidas: label option tigerpila.Pila = tigerpila.nuevaPila1 NONE
in
	val pushSalida = tigerpila.pushPila salidas
	fun popSalida() = tigerpila.popPila salidas
	fun topSalida() =
		case tigerpila.topPila salidas of
		SOME l => l
		| NONE => raise Fail "break incorrecto!"			
end

val datosGlobs = ref ([]: frag list)
fun procEntryExit{level: level, body} =
	let	val label = STRING(name(#frame level), "")
		val body' = PROC{frame= #frame level, body=unNx body}
		val final = STRING(";;-------", "")
	in	datosGlobs:=(!datosGlobs@[label, body', final]) end
fun getResult() = !datosGlobs

fun stringLen s =
	let	fun aux[] = 0
		| aux(#"\\":: #"x"::_::_::t) = 1+aux(t)
		| aux(_::t) = 1+aux(t)
	in	aux(explode s) end

fun stringExp(s: string) =
	let	val l = newlabel()
		val len = ".long "^makestring(stringLen s) : string (* .long 3*)
		val str = ".string \""^s^"\"" : string (* .string "dia" *)
		val _ = datosGlobs:=(!datosGlobs @ [STRING(l, len), STRING("", str)])
	in	Ex(NAME l) end
	
fun preFunctionDec() =
	(pushSalida(NONE);
	actualLevel := !actualLevel+1)

fun functionDec(e, l, proc) =
	let	val body =
				if proc then unNx e
				else MOVE(TEMP rv, unEx e)
		val body' = procEntryExit1(#frame l, body)
		val () = procEntryExit{body=Nx body', level=l}
	in	Ex(CONST 0) end
	
fun postFunctionDec() =
	(popSalida(); actualLevel := !actualLevel-1)

fun unitExp() = Ex (CONST 0)

fun nilExp() = Ex (CONST 0)

fun intExp i = Ex (CONST i)

(*datatype access = InFrame of int | InReg of tigertemp.label*)
(* A la función tigergrame.exp le paso la cantidad de niveles que debe saltar para llegar al frame donde la variable está definida*)
(* Habría que verificar que esto ande correctamente *)	
fun simpleVar ((acc, nivel) : (access * int)) : exp = Ex (tigerframe.exp acc (getActualLev() - nivel))

fun varDec(acc) = simpleVar(acc, getActualLev())

fun fieldVar(var, field) = 
let
	val a = unEx var
	val i = CONST field
	val ra = newtemp()
	val ri = newtemp()
in
	Ex( ESEQ(seq[MOVE(TEMP ra, a),
		MOVE(TEMP ri, i),
		EXP(externalCall("_checkindex", [TEMP ra, TEMP ri]))],
		MEM(BINOP(PLUS, TEMP ra,
			BINOP(MUL, TEMP ri, CONST tigerframe.wSz)))))
end

(* arr tiene que tener tipo TArray (lo obtenés luego de aplicar trvar), ind es una expresión que debe tener tipo TInt *)
fun subscriptVar(arr, ind) =
let
	val a = unEx arr
	val i = unEx ind
	val ra = newtemp()
	val ri = newtemp()
in
	Ex( ESEQ(seq[MOVE(TEMP ra, a),
		MOVE(TEMP ri, i),
		EXP(externalCall("_checkindex", [TEMP ra, TEMP ri]))],
		MEM(BINOP(PLUS, TEMP ra,
			BINOP(MUL, TEMP ri, CONST tigerframe.wSz)))))
end

fun recordExp l =
let
	val s = CONST (length l)
	val is = map (fn (e,n) => unEx e) l
in
	Ex (externalCall("allocRecord", s :: is))
end

fun arrayExp{size, init} =
let
	val s = unEx size
	val i = unEx init
in
	Ex (externalCall("allocArray", [s, i]))
end

fun callExp(name,ext,isproc,lev, ls : exp list) = 
let
	val sl = CONST 0
	val ls = map unEx ls
in
	case isproc of
		true => Nx (EXP (CALL (NAME name, sl :: ls)))
		| false => Ex (CALL (NAME name, sl :: ls))
end

fun letExp ([], body) = Ex (unEx body)
 |  letExp (inits, body) = Ex (ESEQ(seq inits,unEx body))

fun breakExp() = 
let
	val s = topSalida()
in
	Nx (JUMP (NAME s, [s]))
end (*COMPLETADO*)

fun seqExp ([]:exp list) = Nx (EXP(CONST 0))
	| seqExp (exps:exp list) =
		let
			fun unx [e] = []
				| unx (s::ss) = (unNx s)::(unx ss)
				| unx[] = []
		in
			case List.last exps of
				Nx s =>
					let val unexps = map unNx exps
					in Nx (seq unexps) end
				| Ex e => Ex (ESEQ(seq(unx exps), e))
				| cond => Ex (ESEQ(seq(unx exps), unEx cond))
		end

fun preWhileForExp() = pushSalida(SOME(newlabel()))

fun postWhileForExp() = (popSalida(); ())

fun whileExp {test: exp, body: exp, lev:level} =
let
	val cf = unCx test
	val expb = unNx body
	val (l1, l2, l3) = (newlabel(), newlabel(), topSalida())
in
	Nx (seq[LABEL l1,
		cf(l2,l3),
		LABEL l2,
		expb,
		JUMP(NAME l1, [l1]),
		LABEL l3])
end
(* REVISAR *)
fun forExp {lo, hi, var, body} =
let
	val var = unEx var
	val hi = unEx hi 
	val lo = unEx lo
	val body = unNx body
	val tmp = newtemp()
	val (sigue, sigue1, salida) = (newlabel(), newlabel(), topSalida())
in	 
	Nx (seq [MOVE (var,lo), 
		MOVE (TEMP tmp, hi),
		CJUMP (LE, var, TEMP tmp, sigue, salida),
		LABEL sigue, 
		body, 
		CJUMP (EQ, var, TEMP tmp, salida, sigue1),
		LABEL sigue1, 
		MOVE (var, BINOP (PLUS, var, CONST 1)),
		JUMP (NAME sigue, [sigue]),
		LABEL salida])
end

fun ifThenExp{test, then'} =
let
	val cf = unCx test
	val expthen = unNx then'
	val (t,f) = (newlabel(), newlabel())
in
	Nx (seq[cf(t,f),
		LABEL t,
		expthen,
		LABEL f])
		
end
 (*COMPLETADO*)

fun ifThenElseExp {test,then',else'} =
let
	val cf = unCx test
	val expthen = unEx then'
	val expelse = unEx else'
	val (t,f,r) = (newlabel(), newlabel(), newtemp())
in
	Ex (ESEQ(seq[MOVE(TEMP r, expthen),
			cf(t,f),
		    LABEL f,
		    MOVE(TEMP r, expelse),
		    LABEL t],
		    TEMP r))
end
(*COMPLETADO - DISTINTO A LA CARPETA*)

fun ifThenElseExpUnit {test,then',else'} =
let
	val cf = unCx test
	val expthen = unNx then'
	val expelse = unNx else'
	val (t,f) = (newlabel(), newlabel())
in
	Nx (seq[cf(t,f),
		LABEL t,
		expthen,
		LABEL f,
		expelse])
		
end
(*COMPLETADO*)

fun assignExp{var, exp} =
let
	val v = unEx var
	val vl = unEx exp
in
	Nx (MOVE(v,vl))
end

fun binOpIntExp {left, oper = PlusOp, right} = 
let
	val l = unEx left
	val r = unEx right
in
	Ex (BINOP(PLUS,l,r))
end
	| binOpIntExp {left, oper = MinusOp, right} = 
let
	val l = unEx left
	val r = unEx right
in
	Ex (BINOP(MINUS,l,r))
end
	| binOpIntExp {left, oper = TimesOp, right} = 
let
	val l = unEx left
	val r = unEx right
in
	Ex (BINOP(MUL,l,r))
end
	| binOpIntExp {left, oper = DivideOp, right} = 
let
	val l = unEx left
	val r = unEx right
in
	if (r = CONST 0) then raise Fail "División por cero" else Ex (BINOP(DIV,l,r))
end
	| binOpIntExp {left, oper, right} = raise Fail "Error" 
		(*COMPLETADO - VER LO DE LA DIVISIÓN POR CERO - VER LA EXAUSTIVIDAD*)


fun binOpIntRelExp {left,oper = LtOp,right} =
let
	val l = unEx left
	val r = unEx right
	val (t,f,tmp) = (newlabel(), newlabel(), newtemp())
in
	Ex (ESEQ(seq[MOVE(TEMP tmp, CONST 1),
			CJUMP(LT,l,r,t,f),
		    LABEL f,
		    MOVE(TEMP tmp, CONST 0),
		    LABEL t],
		    TEMP tmp))
end	
	| binOpIntRelExp {left,oper = LeOp,right} =
let
	val l = unEx left
	val r = unEx right
	val (t,f,tmp) = (newlabel(), newlabel(), newtemp())
in
	Ex (ESEQ(seq[MOVE(TEMP tmp, CONST 1),
			CJUMP(LE,l,r,t,f),
		    LABEL f,
		    MOVE(TEMP tmp, CONST 0),
		    LABEL t],
		    TEMP tmp))
end	
	| binOpIntRelExp {left,oper = GtOp,right} =
let
	val l = unEx left
	val r = unEx right
	val (t,f,tmp) = (newlabel(), newlabel(), newtemp())
in
	Ex (ESEQ(seq[MOVE(TEMP tmp, CONST 1),
			CJUMP(GT,l,r,t,f),
		    LABEL f,
		    MOVE(TEMP tmp, CONST 0),
		    LABEL t],
		    TEMP tmp))
end	
	| binOpIntRelExp {left,oper = GeOp,right} =
let
	val l = unEx left
	val r = unEx right
	val (t,f,tmp) = (newlabel(), newlabel(), newtemp())
in
	Ex (ESEQ(seq[MOVE(TEMP tmp, CONST 1),
			CJUMP(GE,l,r,t,f),
		    LABEL f,
		    MOVE(TEMP tmp, CONST 0),
		    LABEL t],
		    TEMP tmp))
end	
	| binOpIntRelExp {left,oper ,right} = raise Fail "Error"
	(* COMPLETADO - VER LA EXAUSTIVIDAD *)

fun binOpStrExp {left,oper,right} =
	let
		val l = unEx left
		val r = unEx right
	in 
		Ex (externalCall("_stringCompare", l , r))
	end
end
