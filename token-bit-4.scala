
import scala.language.implicitConversions    
import scala.language.reflectiveCalls
import scala.annotation.tailrec   

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

type Bits = List[Bit]


abstract class Rexp 
case object ZERO extends Rexp
case object ONE extends Rexp
case class PRED(f: Char => Boolean) extends Rexp
case class ALTS(rs: List[Rexp]) extends Rexp 
case class SEQ(r1: Rexp, r2: Rexp) extends Rexp 
case class STAR(r: Rexp) extends Rexp 
case class RECD(x: String, r: Rexp) extends Rexp

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
  case (CHAR(c), bs) => (Chr(c), bs)
  case (ALT(r1, r2), false::bs) => {
    val (v, bs1) = decode_aux(r1, bs)
    (Left(v), bs1)
  }
  case (ALT(r1, r2), true::bs) => {
    val (v, bs1) = decode_aux(r2, bs)
    (Right(v), bs1)
  }
  case (SEQ(r1, r2), bs) => {
    val (v1, bs1) = decode_aux(r1, bs)
    val (v2, bs2) = decode_aux(r2, bs1)
    (Sequ(v1, v2), bs2)
  }
  case (STAR(r1), false::bs) => {
    val (v, bs1) = decode_aux(r1, bs)
    val (Stars(vs), bs2) = decode_aux(STAR(r1), bs1)
    (Stars(v::vs), bs2)
  }
  case (STAR(_), true::bs) => (Stars(Nil), bs)
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

// nullable function: tests whether the aregular 
// expression can recognise the empty string
def nullable (r: ARexp) : Boolean = r match {
  case AZERO => false
  case AONE(_) => true
  case APRED(_,_) => false
  case AALTS(_, rs) => rs.exists(nullable)
  case ASEQ(_, r1, r2) => nullable(r1) && nullable(r2)
  case ASTAR(_, _) => true
}

def mkepsBC(r: ARexp) : Bits = r match {
  case AONE(bs) => bs
  case AALTS(bs, rs) => {
    val n = rs.indexWhere(nullable)
    bs ++ mkepsBC(rs(n))
  }
  case ASEQ(bs, r1, r2) => bs ++ mkepsBC(r1) ++ mkepsBC(r2)
  case ASTAR(bs, r) => bs ++ List(S)
}

// derivative of a regular expression w.r.t. a character
def der(c: Char, r: ARexp) : ARexp = r match {
  case AZERO => AZERO
  case AONE(_) => AZERO
  case APRED(bs, f) => if (f(c)) AONE(bs) else AZERO
  case AALTS(bs, rs) => AALTS(bs, rs.map(der(c, _)))
  case ASEQ(bs, r1, r2) => 
    if (nullable(r1)) AALT(bs, ASEQ(Nil, der(c, r1), r2), fuse(mkepsBC(r1), der(c, r2)))
    else ASEQ(bs, der(c, r1), r2)
  case ASTAR(bs, r) => ASEQ(bs, fuse(List(S), der(c, r)), ASTAR(Nil, r))
}

// derivative w.r.t. a string (iterates der)
@tailrec
def ders (s: List[Char], r: ARexp) : ARexp = s match {
  case Nil => r
  case c::s => ders(s, der(c, r))
}

// main unsimplified lexing function (produces a value)
def lex(r: ARexp, s: List[Char]) : Bits = s match {
  case Nil => if (nullable(r)) mkepsBC(r) else throw new Exception("Not matched")
  case c::cs => lex(der(c, r), cs)
}

def pre_lexing(r: Rexp, s: String) = lex(internalise(r), s.toList)
//def lexing(r: Rexp, s: String) : Val = decode(r, lex(internalise(r), s.toList))


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
  case c::s => ders_simp(s, simp(der(c, r)))
}

def lex_simp(r: ARexp, s: List[Char]) : Bits = s match {
  case Nil => {
    if (nullable(r)) {
      //println(asize(r))
      mkepsBC(r)
    }
   else throw new Exception("Not matched")
  }
  case c::cs => lex_simp(simp(der(c, r)), cs)
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
//def lexing_simp(r: Rexp, s: String) : Val = decode(r, lex_simp(internalise(r), s.toList))





// Lexing Rules for a Small While Language

//symbols
val SYM = PRED("abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ".contains(_))
//digits
val DIGIT = PRED("0123456789".contains(_))
//identifiers
val ID = SYM ~ (SYM | DIGIT).% 
//numbers
val NUM = PLUS(DIGIT)
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
//  env(lexing_simp(r, s)).filterNot { _._1 == "w"}


//reads the string from a file 
//def fromFile(name: String) : String = 
//  io.Source.fromFile(name).mkString

//def tokenise_file(r: Rexp, name: String) = 
//  tokenise(r, fromFile(name))
 

// Some Tests
//============

println("simple tests:")
println(lex(internalise(SYM.%), "abcd".toList))
println(lex(internalise((SYM.%) | NUM), "12345".toList))
println(lex(internalise(WHILE_REGS), "abcd".toList))
println(lex(internalise(WHILE_REGS), "12345".toList))
println(lex(internalise(WHILE_REGS), "\nwrite \"Fib\";".toList))

def time[T](code: => T) = {
  val start = System.nanoTime()
  val result = code
  val end = System.nanoTime()
  println((end - start)/1.0e9)
  result
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
  n := n -x 1
};
write "Result";
write minus2
"""
/*

val prog2 = """
write "Fib";
"""

*/

println("Iteration test with fib")
for (i <- 0 to 1000 by 10) {
  print(i.toString + ":  ")
  time(lex_simp(internalise(WHILE_REGS), (prog2 * i).toList))
}
 
