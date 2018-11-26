import scala.language.implicitConversions    
import scala.language.reflectiveCalls
import scala.annotation.tailrec   

abstract class Bit
case object Z extends Bit
case object S extends Bit

type Bits = List[Bit]

abstract class Rexp 
case object ZERO extends Rexp
case object ONE extends Rexp
case class CHAR(c: Char) extends Rexp
case class ALT(r1: Rexp, r2: Rexp) extends Rexp 
case class SEQ(r1: Rexp, r2: Rexp) extends Rexp 
case class STAR(r: Rexp) extends Rexp 
case class ALTS(rs: List[Rexp]) extends Rexp

abstract class ARexp // {var depth : Int = 0}
case object AZERO extends ARexp
case class AONE(bs: Bits) extends ARexp
case class ACHAR(bs: Bits, c: Char) extends ARexp
case class AALT(bs: Bits, r1: ARexp, r2: ARexp) extends ARexp 
case class ASEQ(bs: Bits, r1: ARexp, r2: ARexp) extends ARexp 
case class ASTAR(bs: Bits, r: ARexp) extends ARexp 
case class AALTS(bs: Bits, rs: List[ARexp]) extends ARexp


abstract class Val
case object Empty extends Val
case class Chr(c: Char) extends Val
case class Sequ(v1: Val, v2: Val) extends Val
case class Left(v: Val) extends Val
case class Right(v: Val) extends Val
case class Stars(vs: List[Val]) extends Val

   
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
}


// nullable function: tests whether the regular 
// expression can recognise the empty string
def nullable (r: Rexp) : Boolean = r match {
  case ZERO => false
  case ONE => true
  case CHAR(_) => false
  case ALT(r1, r2) => nullable(r1) || nullable(r2)
  case SEQ(r1, r2) => nullable(r1) && nullable(r2)
  case STAR(_) => true
}

// derivative of a regular expression w.r.t. a character
def der (c: Char, r: Rexp) : Rexp = r match {
  case ZERO => ZERO
  case ONE => ZERO
  case CHAR(d) => if (c == d) ONE else ZERO
  case ALT(r1, r2) => ALT(der(c, r1), der(c, r2))
  case SEQ(r1, r2) => 
    if (nullable(r1)) ALT(SEQ(der(c, r1), r2), der(c, r2))
    else SEQ(der(c, r1), r2)
  case STAR(r) => SEQ(der(c, r), STAR(r))
}

// derivative w.r.t. a string (iterates der)
def ders (s: List[Char], r: Rexp) : Rexp = s match {
  case Nil => r
  case c::s => ders(s, der(c, r))
}

// mkeps and injection part
def mkeps(r: Rexp) : Val = r match {
  case ONE => Empty
  case ALT(r1, r2) => 
    if (nullable(r1)) Left(mkeps(r1)) else Right(mkeps(r2))
  case SEQ(r1, r2) => Sequ(mkeps(r1), mkeps(r2))
  case STAR(r) => Stars(Nil)
}


def inj(r: Rexp, c: Char, v: Val) : Val = (r, v) match {
  case (STAR(r), Sequ(v1, Stars(vs))) => Stars(inj(r, c, v1)::vs)
  case (SEQ(r1, r2), Sequ(v1, v2)) => Sequ(inj(r1, c, v1), v2)
  case (SEQ(r1, r2), Left(Sequ(v1, v2))) => Sequ(inj(r1, c, v1), v2)
  case (SEQ(r1, r2), Right(v2)) => Sequ(mkeps(r1), inj(r2, c, v2))
  case (ALT(r1, r2), Left(v1)) => Left(inj(r1, c, v1))
  case (ALT(r1, r2), Right(v2)) => Right(inj(r2, c, v2))
  case (CHAR(d), Empty) => Chr(c) 
}

// main lexing function (produces a value)
// - no simplification
def lex(r: Rexp, s: List[Char]) : Val = s match {
  case Nil => if (nullable(r)) mkeps(r) 
              else throw new Exception("Not matched")
  case c::cs => inj(r, c, lex(der(c, r), cs))
}

def lexing(r: Rexp, s: String) : Val = lex(r, s.toList)



// Bitcoded + Annotation
//=======================

// translation into ARexps
def fuse(bs: Bits, r: ARexp) : ARexp = r match {
  case AZERO => AZERO
  case AONE(cs) => AONE(bs ++ cs)
  case ACHAR(cs, c) => ACHAR(bs ++ cs, c)
  case AALT(cs, r1, r2) => AALT(bs ++ cs, r1, r2)
  case ASEQ(cs, r1, r2) => ASEQ(bs ++ cs, r1, r2)
  case ASTAR(cs, r) => ASTAR(bs ++ cs, r)
  case AALTS(cs, rs) => AALTS(bs ++ cs, rs)
}

def internalise(r: Rexp) : ARexp = r match {
  case ZERO => AZERO
  case ONE => AONE(Nil)
  case CHAR(c) => ACHAR(Nil, c)
  case ALT(r1, r2) => 
    AALT(Nil, fuse(List(Z), internalise(r1)), fuse(List(S), internalise(r2)))
  case SEQ(r1, r2) => ASEQ(Nil, internalise(r1), internalise(r2))
  case STAR(r) => ASTAR(Nil, internalise(r))
}
def erase(r: ARexp) : Rexp = {
  r match {
    case AZERO => ZERO
    case AONE(_) => ONE
    case ACHAR(_, c) => CHAR(c)
    case ASEQ(_, r1, r2) => SEQ(erase(r1), erase(r2))
    case ASTAR(_, r) => STAR(erase(r))
    case AALT(_, r1, r2) => ALT(erase(r1), erase(r2))
    case AALTS(_, rs) => ALTS(rs.map(erase(_)))
  }
}
def retrieve(r: ARexp, v: Val) : Bits = (r, v) match {
  case (AONE(bs), Empty) => bs
  case (ACHAR(bs, c), Chr(d)) => bs
  case (AALT(bs, r1, r2), Left(v)) => bs ++ retrieve(r1, v)
  case (AALT(bs, r1, r2), Right(v)) => bs ++ retrieve(r2, v)
  case (ASEQ(bs, r1, r2), Sequ(v1, v2)) => 
    bs ++ retrieve(r1, v1) ++ retrieve(r2, v2)
  case (ASTAR(bs, r), Stars(Nil)) => bs ++ List(S)
  case (ASTAR(bs, r), Stars(v :: vs)) => 
     bs ++ List(Z) ++ retrieve(r, v) ++ retrieve(ASTAR(Nil, r), Stars(vs))
}


def decode_aux(r: Rexp, bs: Bits) : (Val, Bits) = (r, bs) match {
  case (ONE, bs) => (Empty, bs)
  case (CHAR(c), bs) => (Chr(c), bs)
  case (ALT(r1, r2), Z::bs) => {
    val (v, bs1) = decode_aux(r1, bs)
    (Left(v), bs1)
  }
  case (ALT(r1, r2), S::bs) => {
    val (v, bs1) = decode_aux(r2, bs)
    (Right(v), bs1)
  }
  case (SEQ(r1, r2), bs) => {
    val (v1, bs1) = decode_aux(r1, bs)
    val (v2, bs2) = decode_aux(r2, bs1)
    (Sequ(v1, v2), bs2)
  }
  case (STAR(r1), Z::bs) => {
    val (v, bs1) = decode_aux(r1, bs)
    val (Stars(vs), bs2) = decode_aux(STAR(r1), bs1)
    (Stars(v::vs), bs2)
  }
  case (STAR(_), S::bs) => (Stars(Nil), bs)
}

def decode(r: Rexp, bs: Bits) = decode_aux(r, bs) match {
  case (v, Nil) => v
  case _ => throw new Exception("Not decodable")
}

def encode(v: Val) : Bits = v match {
  case Empty => Nil
  case Chr(c) => Nil
  case Left(v) => Z :: encode(v)
  case Right(v) => S :: encode(v)
  case Sequ(v1, v2) => encode(v1) ::: encode(v2)
  case Stars(Nil) => List(S)
  case Stars(v::vs) => Z :: encode(v) ::: encode(Stars(vs))
}


// nullable function: tests whether the aregular 
// expression can recognise the empty string
def bnullable (r: ARexp) : Boolean = r match {
  case AZERO => false
  case AONE(_) => true
  case ACHAR(_,_) => false
  case AALT(_, r1, r2) => bnullable(r1) || bnullable(r2)
  case ASEQ(_, r1, r2) => bnullable(r1) && bnullable(r2)
  case ASTAR(_, _) => true
  case AALTS(_, rs)    => rs.exists(bnullable)
}

def bmkeps(r: ARexp) : Bits = r match {
  case AONE(bs) => bs
  case AALT(bs, r1, r2) => 
    if (bnullable(r1)) bs ++ bmkeps(r1) else bs ++ bmkeps(r2)
  case ASEQ(bs, r1, r2) => bs ++ bmkeps(r1) ++ bmkeps(r2)
  case ASTAR(bs, r) => bs ++ List(S)
  case AALTS(bs, rs) => {
    val n = rs.indexWhere(bnullable)
    bs ++ bmkeps(rs(n))
  }
}

// derivative of a regular expression w.r.t. a character
def bder(c: Char, r: ARexp) : ARexp = r match {
  case AZERO => AZERO
  case AONE(_) => AZERO
  case ACHAR(bs, d) => if (c == d) AONE(bs) else AZERO
  case AALT(bs, r1, r2) => AALT(bs, bder(c, r1), bder(c, r2))
  case ASEQ(bs, r1, r2) => 
    if (bnullable(r1)) 
      AALT(bs, ASEQ(Nil, bder(c, r1), r2), fuse(bmkeps(r1), bder(c, r2)))
    else ASEQ(bs, bder(c, r1), r2)
  case ASTAR(bs, r) => ASEQ(bs, fuse(List(Z), bder(c, r)), ASTAR(Nil, r))
  case AALTS(bs, rs) => AALTS(bs, rs.map(bder(c, _)))
}

def bder_sulz(c: Char, r: ARexp) : ARexp ={
  r match {
  case AZERO => AZERO
  case AONE(_) => AZERO
  case ACHAR(bs, d) => if (c == d) AONE(bs) else AZERO
  case AALT(bs, r1, r2) => AALT(bs, bder_sulz(c, r1), bder_sulz(c, r2))
  case ASEQ(bs, r1, r2) => 
    if (bnullable(r1)) 
      AALTS(bs, List(ASEQ(Nil, bder_sulz(c, r1), r2), fuse(bmkeps(r1), bder_sulz(c, r2))))
    else ASEQ(bs, bder_sulz(c, r1), r2)
  case ASTAR(bs, r) => ASEQ(bs, fuse(List(Z), bder_sulz(c, r)), ASTAR(Nil, r))
  case AALTS(bs, rs) => AALTS(bs, rs.map(bder_sulz(c, _)))
}
}

// derivative w.r.t. a string (iterates der)
@tailrec
def bders (s: List[Char], r: ARexp) : ARexp = s match {
  case Nil => r
  case c::s => bders(s, bder(c, r))
}

// main unsimplified lexing function (produces a value)
def blex(r: ARexp, s: List[Char]) : Bits = s match {
  case Nil => if (bnullable(r)) bmkeps(r) else throw new Exception("Not matched")
  case c::cs => blex(bder(c, r), cs)
}

def pre_blexing(r: ARexp, s: String)  : Bits = blex(r, s.toList)
def blexing(r: Rexp, s: String) : Val = decode(r, pre_blexing(internalise(r), s))

// Simplification .... By Sulzmann and Lu's idea
// is zeroable in Christian's terminology
def isPhi(r: ARexp): Boolean = r match {
  case ASTAR(bs, ri) => false
  case ASEQ(bs, ri1, ri2) => isPhi(ri1) || isPhi(ri2)
  case AALTS(bs, rsi) => rsi.forall(isPhi(_))
  case ACHAR(bs, c) => false
  case AONE(bs) => false
  case AZERO => true
}
def bsimp_I_u(r: ARexp, toplevel: Boolean): ARexp = {
  var fixed_pt_reached = false
  var old = r
  var temp = r
  do {
    temp = bsimp_I(old)
    //if(toplevel){
      //println("Result of this iteration: ")
      //linux_style_tree(temp, 0, List())
    //}

    if (temp == old) fixed_pt_reached = true

    old = temp
  }while(!fixed_pt_reached)
  //println(temp)
  temp
}
//Repeatedly apply simplification until a fixed point is reached (i.e. When we reach case r=>r or AZERO
//or any other shape of regexes that could not be further simplified)
//the commented action in some cases are those that could save a little bit of computation
def bsimp_I(r: ARexp): ARexp = 
{
  r match { 
  case ASEQ(bs1, r1, r2) => r1 match {
    case AONE(bs2) => if(isPhi(r2)) AZERO else fuse((bs1++bs2), r2)//bsimp_I( fuse((bs1 ++ bs2), r2) )
    case _ => if( isPhi(r1) || isPhi(r2) ) AZERO else ASEQ(bs1, bsimp_I_u(r1, false), bsimp_I_u(r2, false))
  }
  case AALTS(bs, la) => la match {
    case Nil => AZERO
    case AALTS(bsp, rs1)::rs2 => AALTS(bs, rs1.map(fuse(bsp, _))++rs2)//bsimp_I(AALTS(bs, rs1.map(fuse(bsp,_)) ++ rs2) )
    case r::Nil => fuse(bs, bsimp_I_u(r, false))
    case r::rs => AALTS(     bs, distinctBy( ((bsimp_I_u(r, false))::(rs.map(bsimp_I_u(_, false))) ).filter(!isPhi(_)), List(), erase(_))   )
  }
  case r => r
  }
}

//def flatten(r: ARexp)
def alt_alts(r: ARexp): ARexp = r match {
  case ASEQ(bs, r1, r2) => ASEQ(bs, alt_alts(r1), alt_alts(r2))
  case AALT(bs, r1, r2) => AALTS( bs, List(alt_alts(r1), alt_alts(r2)) )
  case ASTAR(bs, r)     => ASTAR(bs, alt_alts(r))
  case r => r
}
//simplify after each derivative step
//no AALT is introduced during bder. No need to use alt_alts here
def blex_simp_sulz(r: ARexp, s: List[Char]) : Bits ={
s match {
  case Nil => if (bnullable(r)) bmkeps(r) 
              else throw new Exception("Not matched")
  case c::cs => blex_simp_sulz(bsimp_I_u(bder_sulz(c, r), true), cs)
}
}

//these 3 functions are for testing sizes.
def ders_simp(r: ARexp, s: List[Char]) : ARexp = s match {
  case Nil => r
  case c::cs => ders_simp(bsimp_I_u(bder_sulz(c,r), true), cs)
}
def ders_simp_no_fixed_pt(r: ARexp, s: List[Char]) : ARexp = s match {
  case Nil => r
  case c::cs => ders_simp_no_fixed_pt(bsimp_I(bder_sulz(c,r)), cs)
}

def asize(r: ARexp) : Int = r match {
  case AZERO => 1
  case AONE(_) => 1
  case ACHAR(_,_) => 1
  case ASEQ(bs, r1, r2) => 1 + asize(r1) + asize(r2)
  case AALT(bs, r1, r2) => 1 + asize(r1) + asize(r2)
  case ASTAR(bs, r) => 1 + asize(r)
  case AALTS(bs, rs) => rs.foldLeft(1){(a,b) => a + asize(b)}
}

def blexing_simp_sulz(r: Rexp, s: String) : Val = 
  decode(r, blex_simp_sulz(alt_alts(internalise(r)), s.toList))

// Simplification .... this part has not yet been checked
// whether it works correctly
def bsimp(r: ARexp): ARexp = r match {
  case ASEQ(bs1, r1, r2) => (bsimp(r1), bsimp(r2)) match {
      case (AZERO, _) => AZERO
      case (_, AZERO) => AZERO
      case (AONE(bs2), r2s) => fuse(bs1 ++ bs2, r2s)
      case (r1s, r2s) => ASEQ(bs1, r1s, r2s)
  }
  case AALT(bs1, r1, r2) => (bsimp(r1), bsimp(r2)) match {
      case (AZERO, r2s) => fuse(bs1, r2s)
      case (r1s, AZERO) => fuse(bs1, r1s)
      case (r1s, r2s) => AALT(bs1, r1s, r2s)
  }
  case r => r
}

def blex_simp(r: ARexp, s: List[Char]) : Bits = s match {
  case Nil => if (bnullable(r)) bmkeps(r) 
              else throw new Exception("Not matched")
  case c::cs => blex(bsimp(bder(c, r)), cs)
}

def blexing_simp(r: Rexp, s: String) : Val = 
  decode(r, blex_simp(internalise(r), s.toList))


// Some Simple Tests
//===================

def time_needed[T](i: Int, code: => T) = {
  val start = System.nanoTime()
  for (j <- 1 to i) code
  val end = System.nanoTime()
  (end - start)/(i * 1.0e9)
}
/*

val rf = ("a" | "ab") ~ ("ab" | "")
println(pre_blexing(internalise(rf), "ab"))
println(blexing(rf, "ab"))
println(blexing_simp(rf, "ab"))
println(blexing_simp_sulz(rf,"ab"))

val r0 = ("a" | "ab") ~ ("b" | "")
println(pre_blexing(internalise(r0), "ab"))
println(blexing(r0, "ab"))
println(blexing_simp(r0, "ab"))
println(blexing_simp_sulz(r0,"ab"))

val r1 = ("a" | "ab") ~ ("bcd" | "cd")
println(blexing(r1, "abcd"))
println(blexing_simp(r1, "abcd"))
println(blexing_simp_sulz(r1,"abcd"))

println(blexing((("" | "a") ~ ("ab" | "b")), "ab"))
println(blexing_simp((("" | "a") ~ ("ab" | "b")), "ab"))
println(blexing_simp_sulz((("" | "a") ~ ("ab" | "b")), "ab"))

println(blexing((("" | "a") ~ ("b" | "ab")), "ab"))
println(blexing_simp((("" | "a") ~ ("b" | "ab")), "ab"))
println(blexing_simp_sulz((("" | "a") ~ ("b" | "ab")), "ab"))

println(blexing((("" | "a") ~ ("c" | "ab")), "ab"))
println(blexing_simp((("" | "a") ~ ("c" | "ab")), "ab"))
println(blexing_simp_sulz((("" | "a") ~ ("c" | "ab")), "ab"))

// Sulzmann's tests
//==================

val sulzmann = ("a" | "b" | "ab").%

println(blexing(sulzmann, "a" * 10))
println(blexing_simp(sulzmann, "a" * 10))
println(blexing_simp_sulz(sulzmann, "a" * 10))

for (i <- 1 to 4001 by 500) {
  println(i + ": " + "%.5f".format(time_needed(1, blexing_simp_sulz(sulzmann, "a" * i))))
}

for (i <- 1 to 16 by 5) {
  println(i + ": " + "%.5f".format(time_needed(1, blexing_simp_sulz(sulzmann, "ab" * i))))
}
*/



// Some automatic testing
//========================

def clear() = {
  print("")
  //print("\33[H\33[2J")
}

// enumerates regular expressions until a certain depth
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


//println(enum(2, "ab").size)
//println(enum(3, "ab").size)
//println(enum(3, "abc").size)
//enum(4, "ab").size

import scala.util.Try

def test_mkeps(r: Rexp) = {
  val res1 = Try(Some(mkeps(r))).getOrElse(None)
  val res2 = Try(Some(decode(r, bmkeps(internalise(r))))).getOrElse(None) 
  if (res1 != res2) println(s"Mkeps disagrees on ${r}")
  if (res1 != res2) Some(r) else (None)
}

//println("Testing mkeps")
//enum(2, "ab").map(test_mkeps).toSet
//enum(3, "ab").map(test_mkeps).toSet
//enum(3, "abc").map(test_mkeps).toSet


//enumerates strings of length n over alphabet cs
def strs(n: Int, cs: String) : Set[String] = {
  if (n == 0) Set("")
  else {
    val ss = strs(n - 1, cs)
    ss ++
    (for (s <- ss; c <- cs.toList) yield c + s)
  }
}

//tests lexing and lexing_simp
def tests_blexer_simp(ss: Set[String])(r: Rexp) = {
  clear()
  //println(s"Testing ${r}")
  for (s <- ss.par) yield {
    val res1 = Try(Some(blexing(r, s))).getOrElse(None)
    val res2 = Try(Some(blexing_simp_sulz(r, s))).getOrElse(None)
    if (res1 != res2) println(s"Disagree on ${r} and ${s}")
    if (res1 != res2) println(s"   ${res1} !=  ${res2}")
    if (res1 != res2) Some((r, s)) else None
  }
}
//-------------------------------------------------------------------------------------------------------------DistinctBy Area
def distinctBy[B, C](xs: List[B], acc: List[C], f: B => C): List[B] = {
  xs match {
    case Nil => Nil
    case (x::xs) => {
      if(acc.contains(f(x))) {
        distinctBy(xs, acc, f)  
      }
      else{
        x::distinctBy(xs, f(x)::acc, f)
      }
    }
  } 
}

def even(i: Int): Int = {
  i % 2
}



//-------------------------------------------------------------------------------------------------------------DistinctBy Area


//println(alt_alts(internalise(ALT(CHAR('a'),SEQ(ONE,ZERO)))))
//println(internalise(ALT(CHAR('a'),SEQ(ONE,ZERO))))
//println(blexing_simp_sulz(ALT(CHAR('a'),SEQ(ONE,ZERO)), "a"))

//enum(2, "ab").map(tests_blexer_simp(strs(2, "ab"))).toSet
val rea = STAR("a" | "aa")
val evi = SEQ(STAR(STAR("a")),"b")
//println(blexing(rea, "aaaaaaaaaaaa"))
import scala.collection.mutable.Queue
import scala.collection.mutable.Stack

// main unsimplified lexing function (produces a value): with printing
def print_decode_aux(r: Rexp, bs: Bits) : (Val, Bits) = (r, bs) match {
  case (ONE, bs) => (Empty, bs)
  case (CHAR(c), bs) => (Chr(c), bs)
  case (ALT(r1, r2), Z::bs) => {
    println(bs+" Z signals left in alternative "+r)
    val (v, bs1) = print_decode_aux(r1, bs)
    //println(" :v" + v)
    (Left(v), bs1)
  }
  case (ALT(r1, r2), S::bs) => {
    println(bs+" S signals right in alternative "+r)
    val (v, bs1) = print_decode_aux(r2, bs)
    //println(" v:" + v)
    (Right(v), bs1)
  }
  case (SEQ(r1, r2), bs) => {
    println(bs+" Interpreting sequence "+r)
    val (v1, bs1) = print_decode_aux(r1, bs)
    val (v2, bs2) = print_decode_aux(r2, bs1)
    //println(" v1:"+v1+" v2:"+v2)
    (Sequ(v1, v2), bs2)
  }
  case (STAR(r1), Z::bs) => {
    println(bs+" Z signals one or more iterations in star "+r)
    val (v, bs1) = print_decode_aux(r1, bs)
    val (Stars(vs), bs2) = print_decode_aux(STAR(r1), bs1)
    //println(" v:"+v+" vs"+vs)
    (Stars(v::vs), bs2)
  }
  case (STAR(_), S::bs) => {
    println(bs+" S signals no iterations at all in star "+r)
    //println(" v: Nil")
    (Stars(Nil), bs)
  }
}
def print_decode(r: Rexp, bs: Bits) = print_decode_aux(r, bs) match {
  case (v, Nil) => v
  case _ => throw new Exception("Not decodable")
}
def blex_print(r: ARexp, s: List[Char]) : Bits = {
  linux_style_tree(r, 0, List())
  s match {
    case Nil => if (bnullable(r)) bmkeps(r) else throw new Exception("Not matched")
    case c::cs => {
      println("After derivative of the above aregx against "+c+":") 
      blex_print(bder(c, r), cs)
    }
  }
} 
def blex_simp_sulz_print(r: ARexp, s: List[Char]) : Bits ={
  linux_style_tree(r, 0, List())
  s match {
    case Nil => if (bnullable(r)) bmkeps(r) 
              else throw new Exception("Not matched")
    case c::cs => {
      println("After derivative of the above aregx against "+c+":")
      val der_res = bder_sulz(c, r)
      linux_style_tree(der_res, 0, List())
      println("After simplification of the above aregx: ")
      blex_simp_sulz_print(bsimp_I_u(der_res, true), cs)
    }  
  }
}
//process_print(rea, ("a"*3).toList)
process_print_simp(rea, ("a"*8).toList)
//val evil = STAR(STAR("a"))
//process_print_simp(evi, "aaaaaaaaaaab".toList)

def process_print(r: Rexp, s: List[Char]){
  println("Original regex:")
  tree_for_rexp(r, 0, List())
  println("regex after internalize:")
  val bits = blex_print(alt_alts(internalise(r)), s)
  println("After bmkeps")
  println(bits)
  val V = print_decode(rea,bits)
  print(V)
}

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


def tree_for_rexp(r: Rexp, depth: Int, have_siblings: List[Boolean]):Unit = {
  var current_depth = 0
  if(depth >= 1){
    for (i <- have_siblings)
    {

      if (i)
        print(" "*(current_depth) +"|")
      else
        print(" "*(current_depth + 1))
      current_depth = 3
    }
    print("`--")
  }
  r match {
      case ZERO => print("0\n")
      case ONE => {
        print("e ")

        print("\n")
      }
      case CHAR(c) => {
        print(c+" ")

        print("\n")
      }
      case ALT(r1s, r2s) => {
        print("2 ")

        print("\n")
        tree_for_rexp(r1s, depth + 1, have_siblings:::List(true))
        tree_for_rexp(r2s, depth + 1, have_siblings:::List(false))
      }
      case SEQ(ra1, ra2) => { 
	      print("@ ")
   
        print("\n"); 
	      tree_for_rexp(ra1, depth + 1, have_siblings:::List(true))
	      tree_for_rexp(ra2, depth + 1, have_siblings:::List(false))
      }
      case STAR(ra) => {
	      print("* ")

        print("\n") 
	      tree_for_rexp(ra, depth + 1, have_siblings:::List(false))
      }
  }
}

def linux_style_tree(r: ARexp, depth: Int, have_siblings: List[Boolean]):Unit = {
  var current_depth = 0
  if(depth >= 1){
    for (i <- have_siblings)
    {
      if (i)
        print(" "*(current_depth) +"|")
      else
        print(" "*(current_depth + 1))
      current_depth = 3
    }
    print("`--")
  }
  r match {
      case AZERO => print("0\n")
      case AONE(bs) => {
        print("e ")
        bs.foreach(print(_))
        print("\n")
      }
      case ACHAR(bs, c) => {
        print(c+" ")
        bs.foreach(print(_))
        print("\n")
      }
      case AALT(bs, r1s, r2s) => {
        print("2 ")
        bs.foreach(print(_))
        print("\n")
        linux_style_tree(r1s, depth + 1, have_siblings:::List(true))
        linux_style_tree(r2s, depth + 1, have_siblings:::List(false))
      }
      case AALTS(bs, rs) => {
	      print(rs.length + " ")
        bs.foreach(print(_))
        print("\n")
        val fin = rs.last
	      rs.dropRight(1).foreach(linux_style_tree(_, depth + 1, have_siblings:::List(true)))
        linux_style_tree(fin, depth + 1, have_siblings:::List(false))
      }
      case ASEQ(bs, ra1, ra2) => { 
	      print("@ ")
        bs.foreach(print(_))
        print("\n"); 
	      linux_style_tree(ra1, depth + 1, have_siblings:::List(true))
	      linux_style_tree(ra2, depth + 1, have_siblings:::List(false))
      }
      case ASTAR(bs, ra) => {
	      print("* ")
        bs.foreach(print(_))
        print("\n") 
	      linux_style_tree(ra, depth + 1, have_siblings:::List(false))
      }
  }
}

//asize(ders_simp("".toList, internalise(rea)))
//asize(ders_simp("a".toList, internalise(rea)))
//asize(ders_simp("aa".toList, internalise(rea)))
//asize(ders_simp("aaa".toList, internalise(rea)))
/*
println(asize( ders_simp(alt_alts(internalise(rea)), "aaaaaaaaaaaaa".toList) ))
println(asize( ders_simp_no_fixed_pt(alt_alts(internalise(rea)), "aaaaaaaaaaaaa".toList) ))
println(asize( bders("aaaaaaaaaaaaa".toList, internalise(rea))))
*/
//println("Left to right: simplification till fixed point, simplification only once, and no simp at all")
/*
print(asize( ders_simp(alt_alts(internalise(rea)), ("a"*i).toList) ))
print(" ")
print(asize( ders_simp_no_fixed_pt(alt_alts(internalise(rea)), ("a"*i).toList) ))
print(" ")
println(asize( bders(("a"*i).toList, internalise(rea))))
*/
//var aftder = ders_simp(alt_alts(internalise(rea)), ("a"*i).toList)
//linux_style_tree( aftder, 0, List() )
//print("\n")
//print(bmkeps(aftder))
//print(" ")

//print( ders_simp_no_fixed_pt(alt_alts(internalise(rea)), ("a"*i).toList) )
//print(" ")
//println( bders(("a"*i).toList, internalise(rea)))

//println("Testing lexing 2")
//enum(2, "ab").map(tests_blexer_simp(strs(3, "abc"))).toSet
//println("Testing lexing 3")
//enum(3, "ab").map(tests_blexer_simp(strs(3, "abc"))).toSet

/*

def print_lex(r: Rexp, s: List[Char]) : Val = s match {
  case Nil => if (nullable(r)) print_mkeps(r)
              else throw new Exception("Not matched")
  case c::cs => print_inj(r, c, cs)
}
def print_inj(r: Rexp, c: Char,cs: List[Char]): Val = {
  val inj_res = inj(r, c, print_lex(der(c, r), cs))
  println("injection")  
  println(inj_res) 
  inj_res
}
def print_mkeps(r: Rexp): Val = {
  val how_r_Der_s_matched_E = mkeps(r)
  println("make epsilon")
  println(how_r_Der_s_matched_E) 
  how_r_Der_s_matched_E
}
def how_it_works(r: Rexp, s: String) : Val = print_lex(r, s.toList)
how_it_works( ("a".% ~ "b".%).% ~ "b" , "aab")
*/
