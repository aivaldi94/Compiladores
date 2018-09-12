structure tigermunch :> tigermunch = struct

open tigertemp
open tigerassem
open tigerframe
open tigertree
(* SE CONCATENAN DOS INSTRUCCIONES HACIENDO EMIT;EMIT*)
fun codeGen (frame: tigerframe.frame) (stm:tigertree.stm) : tigerassem.instr list =
let
	val ilist = ref ([] : tigerassem.instr list)
	fun emit x = ilist := x :: !ilist
	fun result (gen) = let val t = tigertemp.newtemp() in gen t; t end

	fun munchStm ((SEQ (a,b)) :tigertree.stm) : unit = (munchStm a; munchStm b)
		(*| munchStm (tigertree.MOVE(MEM(BINOP(PLUS, e1, CONST i)),e2)) = emit(OPER {assem="STORE M[´s0+"^ Int.toString(i) ^ "] <- 's1\n",src=[munchExp e1, munchExp e2],dst=[],jump=NONE})
		| munchStm (tigertree.MOVE(MEM(BINOP(PLUS, CONST i, e1)),e2)) = emit(OPER{assem="STORE M ['s0+"^ Int.toString(i) ^ " ] <- 's1\n",src= [munchExp e1, munchExp e2],dst=[], jump=NONE})
		| munchStm (tigertree.MOVE(MEM(e1),MEM(e2))) = emit (OPER {assem="MOVE M['s0] <-M ['s1]\n",src=[munchExp e1, munchExp e2], dst = [],jump = NONE})
		| munchStm (tigertree.MOVE(MEM(CONST i),e2)) = emit (OPER {assem="STORE M[r0+ "^Int.toString(i) ^ "] <- 's0\n",src=[munchExp e2],dst=[],jump=NONE})
		| munchStm ((tigertree.MOVE(MEM(e1),e2))) = emit (OPER {assem = "STORE M['s0] <- 's1\n",src=[munchExp e1, munchExp e2], dst= [], jump = NONE})*)
		| munchStm (tigertree.MOVE(MEM(e1),MEM(e2))) = emit (OPER {assem="MOV ['s0],['s1]\n",src=[munchExp e1, munchExp e2], dst = [],jump = NONE})
		| munchStm ((tigertree.MOVE(MEM(e1),e2))) = emit (OPER {assem = "MOV ['s0], 's1\n",src=[munchExp e1, munchExp e2], dst= [], jump = NONE})
		| munchStm (tigertree.MOVE (TEMP i,e2)) = emit (OPER {assem="MOV 'd0, 's0\n",src=[munchExp e2],dst=[i],jump=NONE})
		| munchStm (LABEL lab) = emit(tigerassem.LABEL {assem=lab ^ ":\n",lab=lab})
		| munchStm (EXP (CALL (e,args))) = emit (OPER {assem="CALL 's0\n",src=munchExp(e)::munchArgs(0,args),dst=calldefs,jump=NONE})
		| munchStm (_) = emit (OPER {assem = "Falta\n",src=[],dst=[],jump=NONE})
		(*   | BINOP of binop*exp*exp
		     | MEM of exp
		     | CALL of exp*exp list 
		     OJO CON DIVISION CASO ESPECIAL*)
	and munchExp (CONST i) = result (fn r => emit (OPER {assem = "MOV d0,"^ Int.toString(i) ^ "\n",src=[],dst=[r],jump=NONE})) (*Improblable que entre *)
		| munchExp (TEMP t) = t
		| munchExp (NAME l) = result (fn r => emit (OPER {assem = "MOV d0,"^l^ "\n",src=[],dst=[r],jump=NONE})) (*Improblable que entre *)
		(*| munchExp (BINOP(PLUS,TEMP t,CONST i)) = (emit (OPER{assem="ADD 'd0, "^ Int.toString(i) ^ "\n",src=[], dst=[t],jump=NONE});t)*) 
		| munchExp (BINOP(PLUS,CONST i,CONST j)) = result (fn r => emit (OPER{assem="ADD 'd0, "^ Int.toString(i+j) ^ "\n",src=[], dst=[r], jump=NONE})) (*Improblable que entre *)
		| munchExp (BINOP(PLUS,TEMP t,e1)) =  result (fn r=> emit (OPER{assem="ADD 'd0, 's0" ^ "\n",src=[munchExp e1], dst=[r],jump=NONE}))
		 (*(emit (OPER{assem="ADD 'd0, 's0" ^ "\n",src=[munchExp e1], dst=[t],jump=NONE});t)*)
		| munchExp (BINOP(PLUS,e1, TEMP t)) = result (fn r=> emit (OPER{assem="ADD 'd0, 's0" ^ "\n",src=[munchExp e1], dst=[r],jump=NONE}))
		 (*(emit (OPER{assem="ADD 'd0, 's0" ^ "\n",src=[munchExp e1], dst=[t],jump=NONE});t)*)
		(*| munchExp (MEM (BINOP(PLUS,e1,CONST i))) = result (fn r => emit(OPER{assem="LOAD 'd0 <- M ['s0+"^Int.toString(i) ^ "]\n",src=[munchExp e1],dst=[r],jump =NONE}))
		| munchExp (MEM (BINOP (PLUS,CONST i, e1))) = result (fn r => emit (OPER {assem = "LOAD 'd0 <- M['s0+"^ Int.toString(i)^"]\n",src=[munchExp e1],dst=[r],jump=NONE}))
		| munchExp (MEM (CONST i)) = result (fn r => emit (OPER {assem="LOAD 'd0 <- M[r0+"^ Int.toString(i)  ^"]\n",src=[],dst=[r],jump=NONE}))*)
		| munchExp (MEM (e1)) = result(fn r => emit(OPER {assem="MOV 'd0, ['s0]\n",src=[munchExp e1], dst=[r],jump=NONE}))		
		| munchExp (_) = (result (fn r => emit (OPER {assem = "Falta\n",src=[],dst=[],jump=NONE})))
	and munchArgs _ = []
in 
	(munchStm stm; List.rev (!ilist))
end
end
