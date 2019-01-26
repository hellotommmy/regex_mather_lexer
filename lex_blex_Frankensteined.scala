
import scala.language.implicitConversions    
import scala.language.reflectiveCalls
import scala.annotation.tailrec   
import scala.util.Try

def distinctBy[B, C](xs: List[B], f: B => C, acc: List[C] = Nil): List[B] = xs match {
  case Nil => Nil
  case (x::xs) => {
    val res = f(x)
    if (acc.contains(res)) distinctBy(xs, f, acc)  
    else x::distinctBy(xs, f, res::acc)
  }
} 

abstract class Bit
case object Z extends Bit
case object S extends Bit
case class C(c: Char) extends Bit

type Bits = List[Bit]


abstract class Rexp 
case object ZERO extends Rexp
case object ONE extends Rexp
case class PRED(f: Char => Boolean) extends Rexp
case class ALTS(rs: List[Rexp]) extends Rexp 
case class SEQ(r1: Rexp, r2: Rexp) extends Rexp 
case class STAR(r: Rexp) extends Rexp 
case class RECD(x: String, r: Rexp) extends Rexp
//case class ALT(r1: Rexp, r2: Rexp) extends Rexp
//case class PLUS(r: Rexp) extends Rexp

// abbreviations
def CHAR(c: Char) = PRED(_ == c)
def ALT(r1: Rexp, r2: Rexp) = ALTS(List(r1, r2))
def PLUS(r: Rexp) = SEQ(r, STAR(r))

abstract class ARexp 
case object AZERO extends ARexp
case class AONE(bs: Bits) extends ARexp
case class APRED(bs: Bits, f: Char => Boolean) extends ARexp
case class AALTS(bs: Bits, rs: List[ARexp]) extends ARexp 
case class ASEQ(bs: Bits, r1: ARexp, r2: ARexp) extends ARexp 
case class ASTAR(bs: Bits, r: ARexp) extends ARexp 


def AALT(bs: Bits, r1: ARexp, r2: ARexp) = AALTS(bs, List(r1, r2))

abstract class Val
case object Empty extends Val
case class Chr(c: Char) extends Val
case class Sequ(v1: Val, v2: Val) extends Val
case class Left(v: Val) extends Val
case class Right(v: Val) extends Val
case class Stars(vs: List[Val]) extends Val
case class Rec(x: String, v: Val) extends Val
//case class Pos(i: Int, v: Val) extends Val
case object Prd extends Val


   
// some convenience for typing in regular expressions
def charlist2rexp(s : List[Char]): Rexp = s match {
  case Nil => ONE
  case c::Nil => CHAR(c)
  case c::s => SEQ(CHAR(c), charlist2rexp(s))
}
implicit def string2rexp(s : String) : Rexp = charlist2rexp(s.toList)

implicit def RexpOps(r: Rexp) = new {
  def | (s: Rexp) = ALT(r, s)
  def % = STAR(r)
  def ~ (s: Rexp) = SEQ(r, s)
}

implicit def stringOps(s: String) = new {
  def | (r: Rexp) = ALT(s, r)
  def | (r: String) = ALT(s, r)
  def % = STAR(s)
  def ~ (r: Rexp) = SEQ(s, r)
  def ~ (r: String) = SEQ(s, r)
  def $ (r: Rexp) = RECD(s, r)
}

// translation into ARexps
def fuse(bs: Bits, r: ARexp) : ARexp = r match {
  case AZERO => AZERO
  case AONE(cs) => AONE(bs ++ cs)
  case APRED(cs, f) => APRED(bs ++ cs, f)
  case AALTS(cs, rs) => AALTS(bs ++ cs, rs)
  case ASEQ(cs, r1, r2) => ASEQ(bs ++ cs, r1, r2)
  case ASTAR(cs, r) => ASTAR(bs ++ cs, r)
}

def internalise(r: Rexp) : ARexp = r match {
  case ZERO => AZERO
  case ONE => AONE(Nil)
  case PRED(f) => APRED(Nil, f)
  case ALTS(List(r1, r2)) => 
    AALTS(Nil, List(fuse(List(Z), internalise(r1)), fuse(List(S), internalise(r2))))
  case ALTS(r1::rs) => {
     val AALTS(Nil, rs2) = internalise(ALTS(rs))
     AALTS(Nil, fuse(List(Z), internalise(r1)) :: rs2.map(fuse(List(S), _)))
  }
  case SEQ(r1, r2) => ASEQ(Nil, internalise(r1), internalise(r2))
  case STAR(r) => ASTAR(Nil, internalise(r))
  case RECD(x, r) => internalise(r)
}

internalise(("a" | "ab") ~ ("b" | ""))

def decode_aux(r: Rexp, bs: Bits) : (Val, Bits) = (r, bs) match {
  case (ONE, bs) => (Empty, bs)
  case (PRED(f), C(c)::bs) => (Chr(c), bs)
  case (ALTS(r::Nil), bs) => decode_aux(r, bs)
  case (ALTS(rs), bs) => bs match {
    case Z::bs1 => {
      val (v, bs2) = decode_aux(rs.head, bs1)
      (Left(v), bs2)
    }
    case S::bs1 => {
      val (v, bs2) = decode_aux(ALTS(rs.tail), bs1)
      (Right(v), bs2)			
    }
  }
  case (SEQ(r1, r2), bs) => {
    val (v1, bs1) = decode_aux(r1, bs)
    val (v2, bs2) = decode_aux(r2, bs1)
    (Sequ(v1, v2), bs2)
  }
  case (STAR(r1), S::bs) => {
    val (v, bs1) = decode_aux(r1, bs)
    //println(v)
    val (Stars(vs), bs2) = decode_aux(STAR(r1), bs1)
    (Stars(v::vs), bs2)
  }
  case (STAR(_), Z::bs) => (Stars(Nil), bs)
  case (RECD(x, r1), bs) => {
    val (v, bs1) = decode_aux(r1, bs)
    (Rec(x, v), bs1)
  }
}

def decode(r: Rexp, bs: Bits) = decode_aux(r, bs) match {
  case (v, Nil) => v
  case _ => throw new Exception("Not decodable")
}


//erase function: extracts the regx from Aregex
def erase(r:ARexp): Rexp = r match{
  case AZERO => ZERO
  case AONE(_) => ONE
  case APRED(bs, f) => PRED(f)
  case AALTS(bs, rs) => ALTS(rs.map(erase(_)))
  case ASEQ(bs, r1, r2) => SEQ (erase(r1), erase(r2))
  case ASTAR(cs, r)=> STAR(erase(r))
}

//--------------------------------------------------------------------------------------------------------START OF NON-BITCODE PART
// nullable function: tests whether the regular 
// expression can recognise the empty string
def nullable (r: Rexp) : Boolean = r match {
  case ZERO => false
  case ONE => true
  case PRED(_) => false
  case ALTS(rs) => rs.exists(nullable)
  case SEQ(r1, r2) => nullable(r1) && nullable(r2)
  case STAR(_) => true
  case RECD(_, r) => nullable(r)
  //case PLUS(r) => nullable(r)
}

// derivative of a regular expression w.r.t. a character
def der (c: Char, r: Rexp) : Rexp = r match {
  case ZERO => ZERO
  case ONE => ZERO
  case PRED(f) => if (f(c)) ONE else ZERO
  case ALTS(List(r1, r2)) => ALTS(List(der(c, r1), der(c, r2)))
  case SEQ(r1, r2) => 
    if (nullable(r1)) ALTS(List(SEQ(der(c, r1), r2), der(c, r2)))
    else SEQ(der(c, r1), r2)
  case STAR(r) => SEQ(der(c, r), STAR(r))
  case RECD(_, r1) => der(c, r1)
  //case PLUS(r) => SEQ(der(c, r), STAR(r))
}

def flatten(v: Val) : String = v match {
  case Empty => ""
  case Chr(c) => c.toString
  case Left(v) => flatten(v)
  case Right(v) => flatten(v)
  case Sequ(v1, v2) => flatten(v1) + flatten(v2)
  case Stars(vs) => vs.map(flatten).mkString
  case Rec(_, v) => flatten(v)
}

// extracts an environment from a value
def env(v: Val) : List[(String, String)] = v match {
  case Empty => Nil
  case Chr(c) => Nil
  case Left(v) => env(v)
  case Right(v) => env(v)
  case Sequ(v1, v2) => env(v1) ::: env(v2)
  case Stars(vs) => vs.flatMap(env)
  case Rec(x, v) => (x, flatten(v))::env(v)
}


// injection part
def mkeps(r: Rexp) : Val = r match {
  case ONE => Empty
  case ALTS(List(r1, r2)) => 
    if (nullable(r1)) Left(mkeps(r1)) else Right(mkeps(r2))
  case SEQ(r1, r2) => Sequ(mkeps(r1), mkeps(r2))
  case STAR(r) => Stars(Nil)
  case RECD(x, r) => Rec(x, mkeps(r))
  //case PLUS(r) => Stars(List(mkeps(r)))
}

def inj(r: Rexp, c: Char, v: Val) : Val = (r, v) match {
  case (STAR(r), Sequ(v1, Stars(vs))) => Stars(inj(r, c, v1)::vs)
  case (SEQ(r1, r2), Sequ(v1, v2)) => Sequ(inj(r1, c, v1), v2)
  case (SEQ(r1, r2), Left(Sequ(v1, v2))) => Sequ(inj(r1, c, v1), v2)
  case (SEQ(r1, r2), Right(v2)) => Sequ(mkeps(r1), inj(r2, c, v2))
  case (ALTS(List(r1, r2)), Left(v1)) => Left(inj(r1, c, v1))
  case (ALTS(List(r1, r2)), Right(v2)) => Right(inj(r2, c, v2))
  case (PRED(_), Empty) => Chr(c) 
  case (RECD(x, r1), _) => Rec(x, inj(r1, c, v))
  //case (PLUS(r), Sequ(v1, Stars(vs))) => Stars(inj(r, c, v1)::vs)
}
def lex(r: Rexp, s: List[Char]) : Val = s match {
  case Nil => if (nullable(r)) mkeps(r) else throw new Exception("Not matched")
  case c::cs => inj(r, c, lex(der(c, r), cs))
}

def lexing(r: Rexp, s: String) : Val = lex(r, s.toList)

//println(lexing(("ab" | "ab") ~ ("b" | ONE), "ab"))

// some "rectification" functions for simplification
def F_ID(v: Val): Val = v
def F_RIGHT(f: Val => Val) = (v:Val) => Right(f(v))
def F_LEFT(f: Val => Val) = (v:Val) => Left(f(v))
def F_ALT(f1: Val => Val, f2: Val => Val) = (v:Val) => v match {
  case Right(v) => Right(f2(v))
  case Left(v) => Left(f1(v))
}
def F_SEQ(f1: Val => Val, f2: Val => Val) = (v:Val) => v match {
  case Sequ(v1, v2) => Sequ(f1(v1), f2(v2))
}
def F_SEQ_Empty1(f1: Val => Val, f2: Val => Val) = 
  (v:Val) => Sequ(f1(Empty), f2(v))
def F_SEQ_Empty2(f1: Val => Val, f2: Val => Val) = 
  (v:Val) => Sequ(f1(v), f2(Empty))
def F_RECD(f: Val => Val) = (v:Val) => v match {
  case Rec(x, v) => Rec(x, f(v))
}
def F_ERROR(v: Val): Val = throw new Exception("error")

// simplification of regular expressions returning also an
// rectification function; no simplification under STAR 
def simp(r: Rexp): (Rexp, Val => Val) = r match {
  case ALTS(List(r1, r2)) => {
    val (r1s, f1s) = simp(r1)
    val (r2s, f2s) = simp(r2)
    (r1s, r2s) match {
      case (ZERO, _) => (r2s, F_RIGHT(f2s))
      case (_, ZERO) => (r1s, F_LEFT(f1s))
      case _ => if (r1s == r2s) (r1s, F_LEFT(f1s))
                else (ALTS(List(r1s, r2s)), F_ALT(f1s, f2s)) 
    }
  }
  case SEQ(r1, r2) => {
    val (r1s, f1s) = simp(r1)
    val (r2s, f2s) = simp(r2)
    (r1s, r2s) match {
      case (ZERO, _) => (ZERO, F_ERROR)
      case (_, ZERO) => (ZERO, F_ERROR)
      case (ONE, _) => (r2s, F_SEQ_Empty1(f1s, f2s))
      case (_, ONE) => (r1s, F_SEQ_Empty2(f1s, f2s))
      case _ => (SEQ(r1s,r2s), F_SEQ(f1s, f2s))
    }
  }
  case RECD(x, r1) => {
    val (r1s, f1s) = simp(r1)
    (RECD(x, r1s), F_RECD(f1s))
  }
  case r => (r, F_ID)
}

def lex_simp(r: Rexp, s: List[Char]) : Val = s match {
  case Nil => if (nullable(r)) mkeps(r) else throw new Exception("Not matched")
  case c::cs => {
    val (r_simp, f_simp) = simp(der(c, r))
    inj(r, c, f_simp(lex_simp(r_simp, cs)))
  }
}

def lexing_simp(r: Rexp, s: String) : Val = lex_simp(r, s.toList)

println(lexing_simp(("a" | "ab") ~ ("b" | ""), "ab"))

// filters out all white spaces
def tokenise(r: Rexp, s: String) = 
  env(lexing_simp(r, s)).filterNot { _._1 == "w"}


//reads the string from a file 
def fromFile(name: String) : String = 
  io.Source.fromFile(name).mkString

def tokenise_file(r: Rexp, name: String) = 
  tokenise(r, fromFile(name))
 
 //   Testing
//============

def time[T](code: => T) = {
  val start = System.nanoTime()
  val result = code
  val end = System.nanoTime()
  println((end - start)/1.0e9)
  result
}

//--------------------------------------------------------------------------------------------------------END OF NON-BITCODE PART

// bnullable function: tests whether the aregular 
// expression can recognise the empty string
def bnullable (r: ARexp) : Boolean = r match {
  case AZERO => false
  case AONE(_) => true
  case APRED(_,_) => false
  case AALTS(_, rs) => rs.exists(bnullable)
  case ASEQ(_, r1, r2) => bnullable(r1) && bnullable(r2)
  case ASTAR(_, _) => true
}

def mkepsBC(r: ARexp) : Bits = r match {
  case AONE(bs) => bs
  case AALTS(bs, rs) => {
    val n = rs.indexWhere(bnullable)
    bs ++ mkepsBC(rs(n))
  }
  case ASEQ(bs, r1, r2) => bs ++ mkepsBC(r1) ++ mkepsBC(r2)
  case ASTAR(bs, r) => bs ++ List(Z)
}

// derivative of a regular expression w.r.t. a character
def bder(c: Char, r: ARexp) : ARexp = r match {
  case AZERO => AZERO
  case AONE(_) => AZERO
  case APRED(bs, f) => if (f(c)) AONE(bs:::List(C(c))) else AZERO
  case AALTS(bs, rs) => AALTS(bs, rs.map(bder(c, _)))
  case ASEQ(bs, r1, r2) => 
    if (bnullable(r1)) AALT(bs, ASEQ(Nil, bder(c, r1), r2), fuse(mkepsBC(r1), bder(c, r2)))
    else ASEQ(bs, bder(c, r1), r2)
  case ASTAR(bs, r) => ASEQ(bs, fuse(List(S), bder(c, r)), ASTAR(Nil, r))
}


def ders (s: List[Char], r: Rexp) : Rexp = s match {
  case Nil => r
  case c::s => ders(s, der(c, r))
}


// derivative w.r.t. a string (iterates bder)
@tailrec
def bders (s: List[Char], r: ARexp) : ARexp = s match {
  case Nil => r
  case c::s => bders(s, bder(c, r))
}

// main unsimplified lexing function (produces a value)
def blex(r: ARexp, s: List[Char]) : Bits = s match {
  case Nil => if (bnullable(r)) mkepsBC(r) else throw new Exception("Not matched")
  case c::cs => blex(bder(c, r), cs)
}

def bpre_lexing(r: Rexp, s: String) = blex(internalise(r), s.toList)
//def blexing(r: Rexp, s: String) : Val = decode(r, blex(internalise(r), s.toList))


def flats(rs: List[ARexp]): List[ARexp] = rs match {
    case Nil => Nil
    case AZERO :: rs1 => flats(rs1)
    case AALTS(bs, rs1) :: rs2 => rs1.map(fuse(bs, _)) ::: flats(rs2)
    case r1 :: rs2 => r1 :: flats(rs2)
  }

def simp(r: ARexp): ARexp = r match {
  case ASEQ(bs1, r1, r2) => (simp(r1), simp(r2)) match {
      case (AZERO, _) => AZERO
      case (_, AZERO) => AZERO
      case (AONE(bs2), r2s) => fuse(bs1 ++ bs2, r2s)
      case (r1s, r2s) => ASEQ(bs1, r1s, r2s)
  }
  case AALTS(bs1, rs) => distinctBy(flats(rs.map(simp)), erase) match {
    case Nil => AZERO
    case s :: Nil => fuse(bs1, s)
    case rs => AALTS(bs1, rs)  
  }
  case r => r
}

def ders_simp (s: List[Char], r: ARexp) : ARexp = s match {
  case Nil => r
  case c::s => ders_simp(s, simp(bder(c, r)))
}

def blex_simp(r: ARexp, s: List[Char]) : Bits = s match {
  case Nil => {
    if (bnullable(r)) {
      //println(asize(r))
      mkepsBC(r)
    }
   else throw new Exception("Not matched")
  }
  case c::cs => blex_simp(simp(bder(c, r)), cs)
}

//size: of a Aregx for testing purposes 
def size(r: Rexp) : Int = r match {
  case ZERO => 1
  case ONE => 1
  case PRED(_) => 1
  case SEQ(r1, r2) => 1 + size(r1) + size(r2)
  case ALTS(rs) => 1 + rs.map(size).sum
  case STAR(r) => 1 + size(r)
}

def asize(a: ARexp) = size(erase(a))


// decoding does not work yet
def blexing_simp(r: Rexp, s: String) = {
  val bit_code = blex_simp(internalise(r), s.toList)
  //println(s"The length of the string ${s.length}; length of bit sequence:")
  //println((bit_code.length))
  //println(final_derivative)
  //bit_code
  decode(r, bit_code) 
}





// Lexing Rules for a Small While Language

//symbols
val SYM = PRED("abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ".contains(_))
//digits
val DIGIT = PRED("0123456789".contains(_))
//identifiers
val ID = SYM ~ (SYM | DIGIT).% 
//numbers
val NUM = STAR(DIGIT)
//keywords
val KEYWORD : Rexp = "skip" | "while" | "do" | "if" | "then" | "else" | "read" | "write" | "true" | "false"
//semicolons
val SEMI: Rexp = ";"
//operators
val OP: Rexp = ":=" | "==" | "-" | "+" | "*" | "!=" | "<" | ">" | "<=" | ">=" | "%" | "/"
//whitespaces
val WHITESPACE = PLUS(" " | "\n" | "\t")
//parentheses
val RPAREN: Rexp = ")"
val LPAREN: Rexp = "("
val BEGIN: Rexp = "{"
val END: Rexp = "}"
//strings...but probably needs not
val STRING: Rexp = "\"" ~ SYM.% ~ "\""



val WHILE_REGS = (("k" $ KEYWORD) | 
                  ("i" $ ID) | 
                  ("o" $ OP) | 
                  ("n" $ NUM) | 
                  ("s" $ SEMI) | 
                  ("str" $ STRING) |
                  ("p" $ (LPAREN | RPAREN)) | 
                  ("b" $ (BEGIN | END)) | 
                  ("w" $ WHITESPACE)).%

// filters out all white spaces
//def tokenise(r: Rexp, s: String) = 
//  env(blexing_simp(r, s)).filterNot { _._1 == "w"}


//reads the string from a file 
//def fromFile(name: String) : String = 
//  io.Source.fromFile(name).mkString

//def tokenise_file(r: Rexp, name: String) = 
//  tokenise(r, fromFile(name))
 

// Some Tests
//============
/*
println("simple tests:")
println(blexing_simp((SYM.%), "abcd"))
println(blexing_simp(((SYM.%) | ((SYM.% | NUM).%)), "12345"))
println(blexing_simp((WHILE_REGS), "abcd"))
println(blexing_simp((WHILE_REGS), "12345"))
println(blexing_simp((WHILE_REGS), "\nwrite \"Fib\";"))
*/

/*

val prog2 = """
write "Fib";
"""

*/
/*
println("Iteration test with fib")
for (i <- 0 to 120 by 10) {
  print(i.toString + ":  ")
  time(blexing_simp((WHILE_REGS), (prog2 * i)))
  
}
 */

/*
def recurseTest(i:Int):Unit={
   try{
      recurseTest(i+1)
   } catch { case e:java.lang.StackOverflowError => 
      println("Recursion depth on this system is " + i + ".")
   }
}
recurseTest(0)
*/


//--------------------------------------------------------------------------------------------------------START OF NON-BITCODE PART (TESTING)

// Two Simple While programs
//========================
println("prog0 test")

val prog0 = """read n"""
println(env(lexing_simp(WHILE_REGS, prog0)))
println(tokenise(WHILE_REGS, prog0))

println("prog1 test")

val prog1 = """read  n; write (n)"""
println(tokenise(WHILE_REGS, prog1))


// Bigger Tests
//==============

def escape(raw: String): String = {
  import scala.reflect.runtime.universe._
  Literal(Constant(raw)).toString
}

val prog2 = """
write "Fib";
read n;
minus1 := 0;
minus2 := 1;
while n > 0 do {
  temp := minus2;
  minus2 := minus1 + minus2;
  minus1 := temp;
  n := n - 1
};
write "Result";
write minus2
"""

val prog3 = """
start := 1000;
x := start;
y := start;
z := start;
while 0 < x do {
 while 0 < y do {
  while 0 < z do {
    z := z - 1
  };
  z := start;
  y := y - 1
 };     
 y := start;
 x := x - 1
}
"""


println("Tokens of prog2")
println(tokenise(WHILE_REGS, prog2).mkString("\n"))

val fib_tokens = tokenise(WHILE_REGS, prog2)
fib_tokens.map{case (s1, s2) => (escape(s1), escape(s2))}.mkString(",\n")


val test_tokens = tokenise(WHILE_REGS, prog3)
test_tokens.map{case (s1, s2) => (escape(s1), escape(s2))}.mkString(",\n")
/*
println("Iteration test with fib")
for (i <- 0 to 110 by 10) {
  print(i.toString + ":  ")
  time(lexing_simp(WHILE_REGS, prog2 * i))
}
*/



// Tiger Language
//================

//symbols
val TSYM = PRED("abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ".contains(_))
//digits
val TDIGIT = PRED("0123456789".contains(_))
//identifiers
val TID = TSYM ~ (TSYM | TDIGIT | "_").% 
//numbers
val TNUM = PLUS(TDIGIT)
//keywords
val TKEYWORD : Rexp = { "array" | "break" | "do" | "else" | "end" | "for" | 
                        "function" | "if" | "in" | "let" | "nil" | "of" | "then" | 
                        "to" | "type" | "var" | "while" }

//operators
val TOP: Rexp = { "(" | ")" | "[" | "]" | "{" | "}" | ":" | ":=" | "." | "," | 
		  ";" | "/" | "+" | "-" | "=" | "<>" | ">" | "<" | ">=" | "<=" | "&" | "|" }

//whitespaces
val TSPECIAL : Rexp = PRED((""".:=()\;-""" ++ "\"").contains(_))
val TWS : Rexp = " " | "\n" | "\t"
//comments...but probably needs not
val TCOMMENT: Rexp = """/*""" ~ (TSYM | TWS | TSPECIAL | TDIGIT).% ~ """*/"""

val TWHITESPACE : Rexp = PLUS(TWS) | TCOMMENT



//strings...but probably needs not

val TSTRING: Rexp = "\"" ~ (TSYM | " " | TSPECIAL | TDIGIT).% ~ "\""


// for indicating lexing errors
val ERROR = PRED((_) => true)


val TIGER_REGS = (("k" $ TKEYWORD) | 
                  ("i" $ TID) | 
                  ("o" $ TOP) | 
                  ("n" $ TNUM) | 
                  ("str" $ TSTRING) |
                  ("w" $ TWHITESPACE) | 
                  ("err" $ ERROR)).%


//println(tokenise_file(TIGER_REGS, "test.tig").mkString("\n"))
//println(tokenise_file(TIGER_REGS, "queens.tig").mkString("\n"))

//tokenise(TCOMMENT,"""/**/""")
//tokenise(TCOMMENT,"""/*a a a */""")
//tokenise(TIGER_REGS,"""/*a a a */""")
//tokenise(TCOMMENT,"""/* A program to solve the 8-queens problem */""")
//tokenise(TIGER_REGS,"""/* A program to solve the 8-queens problem */""")
//tokenise(TCOMMENT,"""/*  for i:= 0 to c do print("."); print("\n"); flush();*/""")
//tokenise(TIGER_REGS,"""/*  for i:= 0 to c do print("."); print("\n"); flush();*/""")


//--------------------------------------------------------------------------------------------------------END OF NON-BITCODE PART (TESTING)



def clear() = {
  print("")
  //print("\33[H\33[2J")
}

//testing the two lexings produce the same value
//enumerates strings of length n over alphabet cs
def strs(n: Int, cs: String) : Set[String] = {
  if (n == 0) Set("")
  else {
    val ss = strs(n - 1, cs)
    ss ++
    (for (s <- ss; c <- cs.toList) yield c + s)
  }
}
def enum(n: Int, s: String) : Stream[Rexp] = n match {
  case 0 => ZERO #:: ONE #:: s.toStream.map(CHAR)
  case n => {  
    val rs = enum(n - 1, s)
    rs #:::
    (for (r1 <- rs; r2 <- rs) yield ALT(r1, r2)) #:::
    (for (r1 <- rs; r2 <- rs) yield SEQ(r1, r2)) #:::
    (for (r1 <- rs) yield STAR(r1))
  }
}

//tests blexing and lexing
def tests_blexer_simp(ss: Set[String])(r: Rexp) = {
  clear()
  //println(s"Testing ${r}")
  for (s <- ss.par) yield {
    val res1 = Try(Some(lexing_simp(r, s))).getOrElse(None)
    val res2 = Try(Some(blexing_simp(r, s))).getOrElse(None)
    if (res1 != res2) println(s"Disagree on ${r} and ${s}")
    if (res1 != res2) println(s"   ${res1} !=  ${res2}")
    if (res1 != res2) Some((r, s)) else None
  }
}
enum(3, "abc").map(tests_blexer_simp(strs(3, "abc"))).toSet