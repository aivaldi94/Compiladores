signature tigermunch =
sig

val emit: tigerassem.instr -> unit
val munchExp: tigertree.exp -> tigertemp.temp
val munchStm: tigertree.stm -> unit

end
