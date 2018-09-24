structure tigermunch :> tigermunch = struct

open tigertemp
open tigerassem
open tigerframe
open tigertree

fun codeGen (frame: tigerframe.frame) (stm:tigertree.stm) : tigerassem.instr list =
let
	val ITS = Int.toString
	val ilist = ref ([] : tigerassem.instr list)
	
	fun emit x = ilist := x :: !ilist
	
	fun result (gen) = let val t = tigertemp.newtemp() in gen t; t end
	
	fun natToReg 0 = tigerframe.rdi
		| natToReg 1 = tigerframe.rsi
		| natToReg 2 = tigerframe.rdx
		| natToReg 3 = tigerframe.rcx
		| natToReg 4 = tigerframe.r8
		| natToReg 5 = tigerframe.r9
		| natToReg _ = raise Fail "error fatal natToReg"

	fun munchStm s = 
		case s of
			SEQ(a,b) 							=> (munchStm a; munchStm b)
			| EXP (TEMP _) 						=> ()
			| tigertree.MOVE (TEMP t,CONST i) 	=> emit (OPER {assem = "movl $"^ITS(i)^", %'d0\n",src=[], dst= [munchExp (TEMP t)], jump = NONE})
			| tigertree.MOVE (MEM(e1),CONST i) 	=>  emit (OPER {assem = "movl $"^ITS(i)^", (%'d0)\n",src=[], dst= [munchExp e1], jump = NONE})
		    | tigertree.MOVE (MEM(e1),MEM(e2)) 	=> let val t = tigertemp.newtemp () (*¿no debería estar en orden inverso? *)
		                                           in ((emit (OPER {assem="movl (%'s0), %'d0\n",src=[munchExp e2],dst=[t],jump=NONE}));
												        emit (OPER {assem="movl %'s0, (%'s1)\n", src=[t,munchExp e1], dst=[],jump=NONE}))
												   end
			| tigertree.MOVE (TEMP t, CALL(NAME e,args)) => (munchArgs (0,args); (emit (OPER {assem="CALL "^e^"\n",src=[],dst=[],jump=NONE})); 
														     emit (OPER {assem = "movl %'d0, %rax\n",src=[], dst= [munchExp (TEMP t)], jump = NONE}))							   
			| tigertree.MOVE (MEM(e1),e2) => emit (OPER {assem = "movl %'s1, (%'s0)\n",src=[munchExp e1, munchExp e2], dst= [], jump = NONE})
			| tigertree.MOVE (TEMP i,e2) => emit (OPER {assem="movl %'s0, %'d0\n",src=[munchExp e2],dst=[i],jump=NONE})
			| JUMP (NAME n, l) =>  emit (OPER {assem="jmp "^n^"\n",src=[],dst=[],jump=SOME l})
			| JUMP (_, l) =>  emit (OPER {assem="NO COMPLETO jump\n",src=[],dst=[],jump=SOME l})
			| CJUMP (oper,CONST i,CONST j,l1,l2) => let val res = case oper of
																	EQ => i = j
																	| NE => i <> j
																	| LT => i < j
																	| GT => i > j
																	| LE => i <= j
																	| GE => i >= j
																	| ULT => raise Fail "No deberia pasar CJUMP ULT"
																	| ULE => raise Fail "No deberia pasar CJUMP ULE"
																	| UGT => raise Fail "No deberia pasar CJUMP UGT"
																	| UGE => raise Fail "No deberia pasar CJUMP UGE"													
												    in emit (OPER {assem="jmp "^(if res then l1 else l2)^"\n",src=[],dst=[],jump=SOME [if res then l1 else l2]})
												    end	
		    | CJUMP (oper,e1,CONST i,l1,l2) => let val res = case oper of
														  		EQ => "je"
																| NE => "jne"
																| LT => "jl"
																| GT => "jg"
																| LE => "jle"
																| GE => "jge"
																| ULT => raise Fail "No deberia pasar CJUMP ULT"
																| ULE => raise Fail "No deberia pasar CJUMP ULE"
																| UGT => raise Fail "No deberia pasar CJUMP UGT"
																| UGE => raise Fail "No deberia pasar CJUMP UGE"																																									
										       in (emit(OPER {assem="cmp %'s0, "^ITS(i)^"\n",src=[munchExp e1],dst=[],jump=NONE});
										           emit(OPER {assem=res^" "^l1^"\n",src=[],dst=[],jump=SOME [l1,l2]}))
										       end
			| CJUMP (oper,CONST i,e1,l1,l2) => let val res = case oper of
																EQ => "je"
																| NE => "jne"
																| LT => "jl"
																| GT => "jg"
																| LE => "jle"
																| GE => "jge"
																| ULT => raise Fail "No deberia pasar CJUMP ULT"
																| ULE => raise Fail "No deberia pasar CJUMP ULE"
																| UGT => raise Fail "No deberia pasar CJUMP UGT"
																| UGE => raise Fail "No deberia pasar CJUMP UGE"																																									
											   in (emit(OPER {assem="cmp %'s0, "^ITS(i)^"\n",src=[munchExp e1],dst=[],jump=NONE});
												   emit(OPER {assem=res^" "^l1^"\n",src=[],dst=[],jump=SOME [l1,l2]}))
											   end										
			| CJUMP (oper,e1,e2,l1,l2) => let val res = case oper of
															EQ => "JE"
															| NE => "JNE"
															| LT => "JL"
															| GT => "JG"
															| LE => "JLE"
															| GE => "JGE"
															| ULT => raise Fail "No deberia pasar CJUMP ULT"
															| ULE => raise Fail "No deberia pasar CJUMP ULE"
															| UGT => raise Fail "No deberia pasar CJUMP UGT"
															| UGE => raise Fail "No deberia pasar CJUMP UGE"																																										
										   in (emit(OPER {assem="cmp %'s0, %'s1\n",src=[munchExp e1,munchExp e2],dst=[],jump=NONE});
										 	   emit(OPER {assem=res^" "^l1^"\n",src=[],dst=[],jump=SOME [l1,l2]}))
										   end
			| LABEL lab => emit(tigerassem.LABEL {assem=lab^":\n",lab=lab})
			| EXP (CALL (NAME n,args)) => (munchArgs(0,args);(emit (OPER {assem="call "^n^"\n",src=[],dst=[],jump=NONE})))
			| EXP (CALL (e,args)) => raise Fail "No deberia pasar CALL\n"
			| _ => emit (OPER {assem = "Falta\n",src=[],dst=[],jump=NONE})
	(*
	fun munchStm ((SEQ (a,b)) :tigertree.stm) : unit = (munchStm a; munchStm b)
		(*| munchStm (tigertree.MOVE(MEM(BINOP(PLUS, e1, CONST i)),e2)) = emit(OPER {assem="STORE M[´s0+"^ Int.toString(i) ^ "] <- 's1\n",src=[munchExp e1, munchExp e2],dst=[],jump=NONE})
		| munchStm (tigertree.MOVE(MEM(BINOP(PLUS, CONST i, e1)),e2)) = emit(OPER{assem="STORE M ['s0+"^ Int.toString(i) ^ " ] <- 's1\n",src= [munchExp e1, munchExp e2],dst=[], jump=NONE})
		| munchStm (tigertree.MOVE(MEM(e1),MEM(e2))) = emit (OPER {assem="MOVE M['s0] <-M ['s1]\n",src=[munchExp e1, munchExp e2], dst = [],jump = NONE})
		| munchStm (tigertree.MOVE(MEM(CONST i),e2)) = emit (OPER {assem="STORE M[r0+ "^Int.toString(i) ^ "] <- 's0\n",src=[munchExp e2],dst=[],jump=NONE})
		| munchStm ((tigertree.MOVE(MEM(e1),e2))) = emit (OPER {assem = "STORE M['s0] <- 's1\n",src=[munchExp e1, munchExp e2], dst= [], jump = NONE})*)
		| munchStm (EXP(TEMP _)) = ()
		| munchStm (tigertree.MOVE(TEMP t,CONST i)) =  emit (OPER {assem = "movl $"^ITS(i)^", %'d0\n",src=[], dst= [munchExp (TEMP t)], jump = NONE})
		| munchStm (tigertree.MOVE(MEM(e1),CONST i)) =  emit (OPER {assem = "movl $"^ITS(i)^", [%'d0]\n",src=[], dst= [munchExp e1], jump = NONE})
		| munchStm (tigertree.MOVE(MEM(e1),MEM(e2))) = let val t = tigertemp.newtemp () (*¿no debería estar en orden inverso? *)
		                                               in ((emit (OPER {assem="MOV '%d0, [%'s0]\n",src=[munchExp e2],dst=[t],jump=NONE}));
													       emit (OPER {assem="MOV [%'s1], %'s0\n", src=[t,munchExp e1], dst=[],jump=NONE}))
													   end
		| munchStm (tigertree.MOVE(TEMP t, CALL(NAME e,args))) = (munchArgs (0,args); (emit (OPER {assem="CALL "^e^"\n",src=[],dst=[],jump=NONE})); 
																 emit (OPER {assem = "movl %rax, %'d0\n",src=[], dst= [munchExp (TEMP t)], jump = NONE}))							   
		| munchStm ((tigertree.MOVE(MEM(e1),e2))) = emit (OPER {assem = "MOV [%'s0], %'s1\n",src=[munchExp e1, munchExp e2], dst= [], jump = NONE})
		(*| munchStm (tigertree.MOVE (TEMP t,CALL (e,args))) = emit (OPER {assem="MOV 'd0, 's0\n",src=[munchExp e2],dst=[i],jump=NONE})*)
		| munchStm (tigertree.MOVE (TEMP i,e2)) = emit (OPER {assem="MOV %'d0, %'s0\n",src=[munchExp e2],dst=[i],jump=NONE})
		| munchStm (JUMP (NAME n, l)) =  emit (OPER {assem="JMP "^n^"\n",src=[],dst=[],jump=SOME l})
		| munchStm (JUMP (_, l)) =  emit (OPER {assem="NO COMPLETO jump\n",src=[],dst=[],jump=SOME l})
		| munchStm (CJUMP (oper,CONST i,CONST j,l1,l2)) = let val res = case oper of
																	EQ => i = j
																	| NE => i <> j
																	| LT => i < j
																	| GT => i > j
																	| LE => i <= j
																	| GE => i >= j
																	| _ => raise Fail "no deberia pasar (munchStm)"
																	(*| ULT =>
																	| ULE =>
																	| UGT =>
																	| UGE =>*)
														  in emit (OPER {assem="JUMP"^" "^(if res then l1 else l2)^"\n",src=[],dst=[],jump= SOME [if res then l1 else l2]}) end	(*deberia ser [l1,l2]?*)
		| munchStm (CJUMP (oper,e1,CONST i,l1,l2)) = let val res = case oper of
														  		EQ => "JE"
																| NE => "JNE"
																| LT => "JL"
																| GT => "JG"
																| LE => "JLE"
																| GE => "JGE"
																| _ => raise Fail "no deberia pasar (munchStm)"																																												
												in (emit(OPER {assem="CMP %'s0, "^Int.toString(i)^"\n",src=[munchExp e1],dst=[],jump=NONE});emit(OPER{assem=res^" "^l1^"\n",src=[],dst=[],jump=SOME [l1,l2]}))
												end
		| munchStm (CJUMP (oper,CONST i,e1,l1,l2)) = let val res = case oper of
														  		EQ => "JE"
																| NE => "JNE"
																| LT => "JL"
																| GT => "JG"
																| LE => "JLE"
																| GE => "JGE"
																| _ => raise Fail "no deberia pasar (munchStm)"																																												
												in (emit(OPER {assem="cmp %'s0, "^Int.toString(i)^"\n",src=[munchExp e1],dst=[],jump=NONE});emit(OPER{assem=res^" "^l1^"\n",src=[],dst=[],jump=SOME [l1,l2]}))
												end										
		| munchStm (CJUMP (oper,e1,e2,l1,l2)) = let val res = case oper of
														  		EQ => "JE"
																| NE => "JNE"
																| LT => "JL"
																| GT => "JG"
																| LE => "JLE"
																| GE => "JGE"
																| _ => raise Fail "no deberia pasar (munchStm)"																																												
												in (emit(OPER {assem="cmp %'s0, %'s1\n",src=[munchExp e1,munchExp e2],dst=[],jump=NONE});emit(OPER{assem=res^" "^l1^"\n",src=[],dst=[],jump=SOME [l1,l2]}))
												end
		| munchStm (LABEL lab) = emit(tigerassem.LABEL {assem=lab ^ ":\n",lab=lab})
		| munchStm (EXP (CALL (NAME n,args))) = (munchArgs(0,args);(emit (OPER {assem="CALL "^n^"\n",src=[],dst=[],jump=NONE})))
		| munchStm (EXP (CALL (e,args))) = raise Fail "no deberia pasar CALL(e)\n"
		| munchStm (_) = emit (OPER {assem = "Falta\n",src=[],dst=[],jump=NONE})
		(*   | BINOP of binop*exp*exp
		     | MEM of exp
		     | CALL of exp*exp list 
		     OJO CON DIVISION CASO ESPECIAL*)
		     *)
		     
	and munchExp e = case e of
						CONST i => result (fn r => emit (OPER {assem = "movl "^ITS(i)^", %d0\n",src=[],dst=[r],jump=NONE}))
						| TEMP t => t		
						| NAME l => result (fn r => emit (OPER {assem = "movl "^l^", %d0\n",src=[],dst=[r],jump=NONE})) 
						| BINOP(PLUS,CONST i,CONST j) => result (fn r => (emit (OPER{assem="movl "^ITS(i+j)^", %'d0\n",src=[], dst=[r], jump=NONE})))
						| BINOP(MUL,CONST i,CONST j) => result (fn r => (emit (OPER{assem="movl "^ ITS(i*j)^", %'d0\n",src=[], dst=[r], jump=NONE})))
						| BINOP(MINUS,CONST i,CONST j) => result (fn r => (emit (OPER{assem="movl "^ITS(i-j)^", %'d0\n",src=[], dst=[r], jump=NONE})))
						| BINOP(PLUS,TEMP t,e1) => result (fn r=> (emit (OPER {assem = "movl "^t^", %'d0\n",src=[t],dst=[r],jump=NONE});
						                                          (emit (OPER {assem ="addl %'s0, %'d0\n",src=[munchExp e1], dst=[r],jump=NONE}))))
						| BINOP(MUL,TEMP t,e1) => result (fn r=> (emit (OPER {assem = "movl "^t^", %'d0\n",src=[t],dst=[r],jump=NONE});
						                                         (emit (OPER{assem="mul %'s0, %'d0\n",src=[munchExp e1], dst=[r],jump=NONE}))))		 
						| BINOP(PLUS,e1, TEMP t) => result (fn r=> (emit (OPER{assem="add %'s0, %'d0\n",src=[munchExp e1], dst=[r],jump=NONE});
						                                           (emit (OPER {assem = "movl "^t^", %'d0\n",src=[t],dst=[r],jump=NONE}))))		 
						| MEM (CONST i) => result (fn r => emit (OPER {assem="movl ($"^ITS(i)^"), %'d0\n",src=[],dst=[r],jump=NONE}))
						| MEM (e1) => result(fn r => emit(OPER {assem="movl (%'s0), %'d0\n",src=[munchExp e1], dst=[r],jump=NONE}))	
						| _ => result (fn r => emit (OPER {assem = "Falta\n",src=[],dst=[],jump=NONE}))
		     (*
	and munchExp (CONST i) = result (fn r => emit (OPER {assem = "MOV %d0,"^ Int.toString(i) ^ "\n",src=[],dst=[r],jump=NONE})) (*Improblable que entre *)
		| munchExp (TEMP t) = t
		| munchExp (NAME l) = result (fn r => emit (OPER {assem = "MOV %d0,"^l^" $.LC0\n",src=[],dst=[r],jump=NONE})) (*Raro, pero asi dijo guille..revuisar.Improblable que entre *)
		(*| munchExp (BINOP(PLUS,TEMP t,CONST i)) = (emit (OPER{assem="ADD 'd0, "^ Int.toString(i) ^ "\n",src=[], dst=[t],jump=NONE});t)*) 
		| munchExp (BINOP(PLUS,CONST i,CONST j)) = result (fn r => (emit (OPER{assem="MOV %'d0, "^ Int.toString(i+j) ^ "\n",src=[], dst=[r], jump=NONE})))(*result (fn r => (emit (OPER{assem="ADD 'd0, "^ Int.toString(i+j) ^ "\n",src=[], dst=[r], jump=NONE}); emit (OPER{assem="MOV 'd0, 0\n",src=[], dst=[r], jump=NONE})))*)
		| munchExp (BINOP(MUL,CONST i,CONST j)) = result (fn r => (emit (OPER{assem="MOV %'d0, "^ Int.toString(i*j) ^ "\n",src=[], dst=[r], jump=NONE})))
		| munchExp (BINOP(MINUS,CONST i,CONST j)) = result (fn r => (emit (OPER{assem="MOV %'d0, "^ Int.toString(i-j) ^ "\n",src=[], dst=[r], jump=NONE})))(*result (fn r => (emit (OPER{assem="SUB 'd0, "^ Int.toString(i) ^ "\n",src=[], dst=[r], jump=NONE}); emit (OPER{assem="MOV 'd0, "^ Int.toString(j) ^ "\n",src=[], dst=[r], jump=NONE})))*)  (*Improblable que entre *)
		| munchExp (BINOP(PLUS,TEMP t,e1)) =  result (fn r=> (emit (OPER {assem = "MOV %'d0, t\n",src=[t],dst=[r],jump=NONE});(emit (OPER{assem="ADD %'d0, %'s0" ^ "\n",src=[munchExp e1], dst=[r],jump=NONE}))))
		| munchExp (BINOP(MUL,TEMP t,e1)) =  result (fn r=> (emit (OPER {assem = "MOV %'d0, t\n",src=[t],dst=[r],jump=NONE});(emit (OPER{assem="IMUL %'d0, %'s0" ^ "\n",src=[munchExp e1], dst=[r],jump=NONE}))))
		 (*(emit (OPER{assem="ADD 'd0, 's0" ^ "\n",src=[munchExp e1], dst=[t],jump=NONE});t)*)
		| munchExp (BINOP(PLUS,e1, TEMP t)) = result (fn r=> (emit (OPER{assem="ADD %'d0, %'s0" ^ "\n",src=[munchExp e1], dst=[r],jump=NONE});(emit (OPER {assem = "MOV %'d0, t\n",src=[t],dst=[r],jump=NONE}))))
		 (*(emit (OPER{assem="ADD 'd0, 's0" ^ "\n",src=[munchExp e1], dst=[t],jump=NONE});t)*)
		(*| munchExp (MEM (BINOP(PLUS,e1,CONST i))) = result (fn r => emit(OPER{assem="LOAD 'd0 <- M ['s0+"^Int.toString(i) ^ "]\n",src=[munchExp e1],dst=[r],jump =NONE}))
		| munchExp (MEM (BINOP (PLUS,CONST i, e1))) = result (fn r => emit (OPER {assem = "LOAD 'd0 <- M['s0+"^ Int.toString(i)^"]\n",src=[munchExp e1],dst=[r],jump=NONE}))*)
		| munchExp (MEM (CONST i)) = result (fn r => emit (OPER {assem="MOV %'d0, "^Int.toString(i)^"]\n",src=[],dst=[r],jump=NONE}))
		| munchExp (MEM (e1)) = result(fn r => emit(OPER {assem="MOV %'d0, [%'s0]\n",src=[munchExp e1], dst=[r],jump=NONE}))		
		| munchExp (CALL (e,args)) = result (fn r => emit (OPER {assem="CALL %'s0\n",src=[],dst=calldefs,jump=NONE}))
		| munchExp (_) = (result (fn r => emit (OPER {assem = "Falta\n",src=[],dst=[],jump=NONE})))
		*)
	and munchArgs ((_,[]) : (int * exp list)) : unit = ()
		| munchArgs (n,(TEMP x::xs)) = ((if (n<6) then emit (OPER {assem = "movl %"^(natToReg n)^", 's0\n",src=[munchExp (TEMP x)],dst=[natToReg n],jump=NONE}) 
											else emit (OPER {assem = "pushl 's0\n",src=[munchExp (TEMP x)],dst=[],jump=NONE})); munchArgs(n+1,xs))
		| munchArgs (n,(CONST i::xs)) = ((if (n<6) then emit (OPER {assem = "movl %"^(natToReg n)^", "^ITS(i)^"\n",src=[],dst=[natToReg n],jump=NONE}) 
											else emit (OPER {assem = "pushl $"^ITS(i)^"\n",src=[],dst=[],jump=NONE})); munchArgs(n+1,xs))
		| munchArgs (n,(NAME l::xs)) = ((if (n<6) then emit (OPER {assem = "movl %"^(natToReg n)^", "^l^"\n",src=[],dst=[natToReg n],jump=NONE}) 
											else emit (OPER {assem = "pushl $"^l^"\n",src=[],dst=[],jump=NONE})); munchArgs(n+1,xs))
		| munchArgs (n,(MEM(CONST i))::xs) = ((if (n<6) then emit (OPER {assem = "movl %"^(natToReg n)^", "^ITS(i)^"\n",src=[],dst=[natToReg n],jump=NONE}) 
											else emit (OPER {assem = "pushl $"^ITS(i)^"\n",src=[],dst=[],jump=NONE})); munchArgs(n+1,xs))
		| munchArgs _ = emit (OPER {assem = "Falta\n",src=[],dst=[],jump=NONE})
in 
	(munchStm stm; List.rev (!ilist))
end
end
