structure tigermunch :> tigermunch = struct

open tigertemp
open tigerassem
open tigerframe
open tigertree

fun codeGen (frame: tigerframe.frame) (stm:tigertree.stm) : tigerassem.instr list =
let
	val ilist = ref ([] : tigerassem.instr list)
	fun emit x = ilist := x :: !ilist
	fun result (gen) = let val t = tigertemp.newtemp() in gen t; t end

	fun munchStm ((SEQ (a,b)) :tigertree.stm) : unit = (munchStm a; munchStm b)
		| munchStm (tigertree.MOVE(MEM(BINOP(PLUS, e1, CONST i)),e2)) = emit(OPER {assem="STORE M[´s0+"^ Int.toString(i) ^ "] <- 's1\n",src=[munchExp e1, munchExp e2],dst=[],jump=NONE})
		| munchStm (tigertree.MOVE(MEM(BINOP(PLUS, CONST i, e1)),e2)) = emit(OPER{assem="STORE M ['s0+"^ Int.toString(i) ^ " ] <- 's1\n",src= [munchExp e1, munchExp e2],dst=[], jump=NONE})
		| munchStm (tigertree.MOVE(MEM(e1),MEM(e2))) = emit (OPER {assem="MOVE M['s0] <-M ['s1]\n",src=[munchExp e1, munchExp e2], dst = [],jump = NONE})
		| munchStm (tigertree.MOVE(MEM(CONST i),e2)) = emit (OPER {assem="STORE M[r0+ "^Int.toString(i) ^ "] <- 's0\n",src=[munchExp e2],dst=[],jump=NONE})
		| munchStm ((tigertree.MOVE(MEM(e1),e2))) = emit (OPER {assem = "STORE M['s0] <- 's1\n",src=[munchExp e1, munchExp e2], dst= [], jump = NONE})
		| munchStm (MOVE (TEMP i,e2)) = emit (OPER {assem="ADD 'd0 <- 's0 + r0\n",src=[munchExp e2],dst=[i],jump=NONE})
		| munchStm (LABEL lab) = emit(tigerassem.LABEL {assem=lab ^ ":\n",lab=lab})
		| munchStm (EXP (CALL (e,args))) = emit (OPER {assem="CALL 's0\n",src=munchExp(e)::munchArgs(0,args),dst=calldefs,jump=NONE})
	and munchExp (MEM (BINOP(PLUS,e1,CONST i))) = result (fn r => emit(OPER{assem="LOAD 'd0 <- M ['s0+"^Int.toString(i) ^ "]\n",src=[munchExp e1],dst=[r],jump =NONE}))
		| munchExp (MEM (BINOP (PLUS,CONST i, e1))) = result (fn r => emit (OPER {assem = "LOAD 'd0 <- M['s0+"^ Int.toString(i)^"]\n",src=[munchExp e1],dst=[r],jump=NONE}))
		| munchExp (MEM (CONST i)) = result (fn r => emit (OPER {assem="LOAD 'd0 <- M[r0+"^ Int.toString(i)  ^"]\n",src=[],dst=[r],jump=NONE}))
		| munchExp (MEM (e1)) = result(fn r => emit(OPER {assem="LOAD 'd0 <- M['s0+0]\n",src=[munchExp e1], dst=[r],jump=NONE}))
		| munchExp (BINOP(PLUS,e1,CONST i)) = result (fn r => emit (OPER{assem="ADDI 'd0 <- 's0+" ^ Int.toString(i) ^ "\n",src=[munchExp e1], dst=[r],jump=NONE}))
		| munchExp (BINOP (PLUS, CONST i, e1)) = result (fn r => emit (OPER {assem = "ADDI 'd0 <- 's0+"^ Int.toString(i) ^ "\n",src=[munchExp e1], dst=[r], jump=NONE}))
		| munchExp (CONST i) = result (fn r => emit (OPER {assem = "ADDI 'd0 <- 'r0"^ Int.toString(i) ^ "\n",src=[],dst=[r],jump=NONE}))
		| munchExp (BINOP(PLUS,e1,e2)) = result (fn r => emit (OPER {assem="ADD 'd0 <- 's0+'s1\n",src=[munchExp e1, munchExp e2],dst=[r],jump=NONE}))
		| munchExp (TEMP t) = t
		(* |munchExp (BINOP (MUL (jm )))*)
	
	and munchArgs _ = []
in 
	(munchStm stm; List.rev (!ilist))
end
end
