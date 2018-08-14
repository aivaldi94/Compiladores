structure tigermunch :> tigermunch = struct

open tigertree
open tigertemp
open tigerassem

val ilist = ref ([] : tigerassem.instr list)
fun emit x = ilist := x :: !ilist

fun munchStm(SEQ (a,b)) = (munchStm a, munchStm b)
	| munchStm (MOVE(MEM(BINOP(PLUS, e1, CONST i)),e2)) = emit(OPER {assem="STORE M[´s0+"^ int i ^ "] <- 's1\n",src=[munchExp e1, munchExp e2],dst=[],jump=NONE})
	| munchStm (MOVE (MEM(BINOP(PLUS, CONT i, e1)),e2)) = emit(OPER{assem="STORE M ['s0+"^ int i ^ " ] <- 's1\n",src= [munchExp e1, munchExp e2],dst=[], jump=NONE})
	| munchStm (MOVE(MEM(e1),MEM(e2))) = emit (OPER {assem="MOVE M['s0] <-M ['s1]\n",src=[munchExp e1, munchExp e2], dst = [],jump = NONE})
	| munchStm (MOVE(MEM(CONST i),e2)) = emit (OPER {assem="STORE M[r0+ "^ int i ^ "] <- 's0\n",src=[munchExp e2],dst=[],jump=NONE})
	| munchStm ((MOVE(MEM(e1)),e2)) = emit (OPER {assem = "STORE M['s0] <- 's1\n",src=[muncExp e1, munchExp e2], dst= [], jump = NONE})
	| munchStm (MOVE (TEMP i,e2)) = emit (OPER {assem="ADD 'd0 <- 's0 + r0\n",src=[munchExp e2],dst=[i],jump=NONE})
	| munchStm (LABEL lab) = emit(LABEL {assem=lab ^ ":\n",lab=lab})
	| munchStm (EXP (CALL (e,args))) = emit (OPER {assem="CALL 's0\n",sec=muncExp(e)::munchArgs(0,args),dst=calldefs,jump=NONE})


fun result (gen) = let val t = tigertemp.newtemp() in gen t; t end

fun munchExp (MEM (BINOP(PLUS,e1,CONST i))) = result (fn r => emit(OPER{assem="LOAD 'd0 <- M ['s0+"^ int i ^ "]\n",src=[munchExp e1],dst=[r],jump =NONE}))
	| munchExp (MEM (BINOP (PLUS,CONST i, e1))) = result (fn r => emit (OPER {assem = "LOAD 'd0 <- M['s0+"^int i^"]\n",src=[munchExp e1],dst=[r],jump=NONE}))
	| munchExp (MEM (CONST i)) = result (fn r => emit (OPER {assem="LOAD 'd0 <- M[r0+"^int i ^"]\n",src=[],dst[r],jump=NONE}))
	| munchExp (MEM (e1)) = result(fn r => emit(OPER {assem="LOAD 'd0 <- M['s0+0]\n",src=[munchExp e1], dst=[r],jump=NONE}))
	| munchExp (BINOP(PLUS,e1,CONST i)) = result (fn r => emit (OPER{assem="ADDI 'd0 <- 's0+" ^ int i ^ "\n",src=[munchExp e1], dst=[r],jump=NONE}))
	| munchExp (BINOP (PLUS, CONST i, e1)) = result (fn r => emit (OPER {assem = "ADDI 'd0 <- 's0+"^int i^ "\n",src=[munchExp e1], dst=[r], jump=NONE}))
	| munchExp (CONST i) = result (fn r => emit (OPER {assem = "ADDI 'd0 <- 'r0"^ int i ^ "\n",src=[],dst=[r],jump=NONE}))
	| munchExp (BINOP(PLUS,e1,e2)) = result (fn r => emit (OPER {assem="ADD 'd0 <- 's0+'s1\n",src=[munchExp e1, munchExp e2],dst=[r],jump=NONE}))
	| munchExp (TEMP t) = t
