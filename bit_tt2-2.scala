
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


abstract class Rexp 
case object ZERO extends Rexp
case object ONE extends Rexp
case class CHAR(c: Char) extends Rexp
case class ALTS(rs: List[Rexp]) extends Rexp 
case class SEQ(r1: Rexp, r2: Rexp) extends Rexp 
case class STAR(r: Rexp) extends Rexp 
case class RECD(x: String, r: Rexp) extends Rexp

def ALT(r1: Rexp, r2: Rexp) = ALTS(List(r1,r2))

abstract class ARexp 
case object AZERO extends ARexp
case class AONE(bs: List[Boolean]) extends ARexp
case class ACHAR(bs: List[Boolean], c: Char) extends ARexp
case class AALTS(bs: List[Boolean], rs: List[ARexp]) extends ARexp 
case class ASEQ(bs: List[Boolean], r1: ARexp, r2: ARexp) extends ARexp 
case class ASTAR(bs: List[Boolean], r: ARexp) extends ARexp 


def AALT(bs: List[Boolean], r1: ARexp, r2: ARexp) = AALTS(bs, List(r1,r2))

abstract class Val
case object Empty extends Val
case class Chr(c: Char) extends Val
case class Sequ(v1: Val, v2: Val) extends Val
case class Left(v: Val) extends Val
case class Right(v: Val) extends Val
case class Stars(vs: List[Val]) extends Val
case class Rec(x: String, v: Val) extends Val


abstract class Bit
case object Z extends Bit
case object S extends Bit

type Bits = List[Bit]
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

def strs(n: Int, cs: String) : Set[String] = {
  if (n == 0) Set("")
  else {
    val ss = strs(n - 1, cs)
    ss ++
    (for (s <- ss; c <- cs.toList) yield c + s)
  }
}
 
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
def fuse(bs: List[Boolean], r: ARexp) : ARexp = r match {
  case AZERO => AZERO
  case AONE(cs) => AONE(bs ++ cs)
  case ACHAR(cs, c) => ACHAR(bs ++ cs, c)
  case AALTS(cs, rs) => AALTS(bs ++ cs, rs)
  case ASEQ(cs, r1, r2) => ASEQ(bs ++ cs, r1, r2)
  case ASTAR(cs, r) => ASTAR(bs ++ cs, r)
}

def internalise(r: Rexp) : ARexp = r match {
  case ZERO => AZERO
  case ONE => AONE(Nil)
  case CHAR(c) => ACHAR(Nil, c)
  case ALTS(List(r1, r2)) => AALTS(Nil, List(fuse(List(false), internalise(r1)), fuse(List(true), internalise(r2))))
  case ALTS(r1::rs) => {
     val AALTS(Nil, rs2) = internalise(ALTS(rs))
     AALTS(Nil, fuse(List(false), internalise(r1)) :: rs2.map(fuse(List(true), _)))
  }
  case SEQ(r1, r2) => ASEQ(Nil, internalise(r1), internalise(r2))
  case STAR(r) => ASTAR(Nil, internalise(r))
  case RECD(x, r) => internalise(r)
}

internalise(("a" | "ab") ~ ("b" | ""))

/*
def decode_aux(r: Rexp, bs: List[Boolean]) : (Val, List[Boolean]) = (r, bs) match {
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

def decode(r: Rexp, bs: List[Boolean]) = decode_aux(r, bs) match {
  case (v, Nil) => v
  case _ => throw new Exception("Not decodable")
}
*/

//erase function: extracts the regx from Aregex
def erase(r:ARexp): Rexp = r match{
  case AZERO => ZERO
  case AONE(_) => ONE
  case ACHAR(bs, c) => CHAR(c)
  case AALTS(bs, rs) => ALTS(rs.map(erase(_)))
  case ASEQ(bs, r1, r2) => SEQ (erase(r1), erase(r2))
  case ASTAR(cs, r)=> STAR(erase(r))
}

// nullable function: tests whether the aregular 
// expression can recognise the empty string
def nullable (r: ARexp) : Boolean = r match {
  case AZERO => false
  case AONE(_) => true
  case ACHAR(_,_) => false
  case AALTS(_, rs) => rs.exists(nullable)
  case ASEQ(_, r1, r2) => nullable(r1) && nullable(r2)
  case ASTAR(_, _) => true
}

def mkepsBC(r: ARexp) : List[Boolean] = r match {
  case AONE(bs) => bs
  case AALTS(bs, rs) => {
    val n = rs.indexWhere(nullable)
    bs ++ mkepsBC(rs(n))
  }
  case ASEQ(bs, r1, r2) => bs ++ mkepsBC(r1) ++ mkepsBC(r2)
  case ASTAR(bs, r) => bs ++ List(true)
}

// derivative of a regular expression w.r.t. a character
def der (c: Char, r: ARexp) : ARexp = r match {
  case AZERO => AZERO
  case AONE(_) => AZERO
  case ACHAR(bs, d) => if (c == d) AONE(bs) else AZERO
  case AALTS(bs, rs) => AALTS(bs, rs.map(der(c, _)))
  case ASEQ(bs, r1, r2) => 
    if (nullable(r1)) AALT(bs, ASEQ(Nil, der(c, r1), r2), fuse(mkepsBC(r1), der(c, r2)))
    else ASEQ(bs, der(c, r1), r2)
  case ASTAR(bs, r) => ASEQ(bs, fuse(List(false), der(c, r)), ASTAR(Nil, r))
}

// derivative w.r.t. a string (iterates der)
@tailrec
def ders (s: List[Char], r: ARexp) : ARexp = s match {
  case Nil => r
  case c::s => ders(s, der(c, r))
}

// main unsimplified lexing function (produces a value)
def lex(r: ARexp, s: List[Char]) : List[Boolean] = s match {
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
  case AALTS(bs1, rs) => distinctBy(flats(rs.map(simp(_))), erase) match {
    case Nil => AZERO
    case rs => AALTS(bs1, rs)  
  }
  case r => r
}

def ders_simp (s: List[Char], r: ARexp) : ARexp = s match {
  case Nil => r
  case c::s => ders_simp(s, simp(der(c, r)))
}

def lex_simp(r: ARexp, s: List[Char]) : List[Boolean] = s match {
  case Nil => if (nullable(r)) mkepsBC(r) else throw new Exception("Not matched")
  case c::cs => lex(simp(der(c, r)), cs)
}

//def lexing_simp(r: Rexp, s: String) : Val = decode(r, lex_simp(internalise(r), s.toList))


// Some Tests
//============

def time_needed[T](i: Int, code: => T) = {
  val start = System.nanoTime()
  for (j <- 1 to i) code
  val end = System.nanoTime()
  (end - start)/(i * 1.0e9)
}

//size: of a Aregx for testing purposes 
def size(r: Rexp) : Int = r match {
  case ZERO => 1
  case ONE => 1
  case CHAR(_) => 1
  case SEQ(r1, r2) => 1 + size(r1) + size(r2)
  case ALTS(rs) => 1 + rs.map(size).sum
  case STAR(r) => 1 + size(r)
}

def asize(a: ARexp) = size(erase(a))


// string of a regular expressions - for testing purposes
  def string(r: Rexp): String = r match {
    case ZERO => "0"
    case ONE => "1"
    case CHAR(c) => c.toString
    case ALTS(rs) => rs.map(string).mkString("[", "|", "]")
    case SEQ(CHAR(c), CHAR(d)) => s"${c}${d}"
    case SEQ(ONE, CHAR(c)) => s"1${c}"
    case SEQ(r1, r2) => s"(${string(r1)} ~ ${string(r2)})"
    case STAR(r) => s"(${string(r)})*"
  }


//testing SEQ(STAR(STAR(CHAR('a'))), CHAR('b'))
val EVILR = SEQ(STAR(STAR(CHAR('a'))), CHAR('b'))

string(erase(ders_simp("".toList, internalise(EVILR))))
string(erase(ders_simp("a".toList, internalise(EVILR))))
string(erase(ders_simp("aa".toList, internalise(EVILR))))
string(erase(ders_simp("aaa".toList, internalise(EVILR))))
string(erase(ders_simp("aaaaaa".toList, internalise(EVILR))))
string(erase(ders_simp("aaaaaaaaa".toList, internalise(EVILR))))
string(erase(ders_simp("aaaaaaaaaaaa".toList, internalise(EVILR))))

size(erase(ders_simp("".toList, internalise(EVILR))))
size(erase(ders_simp("a".toList, internalise(EVILR))))
size(erase(ders_simp("aa".toList, internalise(EVILR))))
size(erase(ders_simp("aaa".toList, internalise(EVILR))))
size(erase(ders_simp("aaaaaa".toList, internalise(EVILR))))
size(erase(ders_simp("aaaaaaaaa".toList, internalise(EVILR))))
size(erase(ders_simp("aaaaaaaaaaaa".toList, internalise(EVILR))))

(ders("".toList, internalise(EVILR)))
(ders("a".toList, internalise(EVILR)))
(ders("aa".toList, internalise(EVILR)))
(ders("aaa".toList, internalise(EVILR)))
(ders("aaaaaa".toList, internalise(EVILR)))
(ders("aaaaaaaaa".toList, internalise(EVILR)))
(ders("aaaaaaaaaaaa".toList, internalise(EVILR)))

//Testing STAR("a" | "aa")
val rea = STAR("a" | "aa")
string(erase(ders_simp("".toList, internalise(rea))))
string(erase(ders_simp("a".toList, internalise(rea))))
string(erase(ders_simp("aa".toList, internalise(rea))))
string(erase(ders_simp("aaa".toList, internalise(rea))))
string(erase(ders_simp("aaaaaa".toList, internalise(rea))))
string(erase(ders_simp("aaaaaaaaa".toList, internalise(rea))))
string(erase(ders_simp("aaaaaaaaaaaa".toList, internalise(rea))))
string(erase(ders_simp("aaaaaabaaaabbbbbaaaaaaaaaaaaaaa".toList, internalise(rea))))

def tests_blexer_simp(ss: Set[String])(r: Rexp) = {
  clear()
  //println(s"Testing ${r}")
  for (s <- ss.par) yield {
    val res1 = Try(Some(lex(internalise(r), s.toList))).getOrElse(None)
    val res2 = Try(Some(lex_simp(internalise(r), s.toList))).getOrElse(None)
    if (res1 != res2) println(s"Disagree on ${r} and ${s}")
    if (res1 != res2) println(s"   ${res1} !=  ${res2}")
    if (res1 != res2) Some((r, s)) else None
  }
}

def clear() = {
  print("")
  //print("\33[H\33[2J")
}
println("Testing lexing 2")
enum(3, "ab").map(tests_blexer_simp(strs(3, "ab"))).toSet

def process_print_simp(r: Rexp, s: List[Char]){
  println("Original regex:")
  tree_for_rexp(r, 0, List())
  println("regex after internalize:")
  val bits = blex_simp_sulz_print(alt_alts(internalise(r)), s)
  println("After bmkeps")
  println(bits)
  val V = print_decode(r,bits)
  print(V)
}
