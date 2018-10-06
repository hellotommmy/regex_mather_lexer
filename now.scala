abstract class Regx
case class ZERO extends Regx
case class ONE extends Regx
case class CHAR(c: Char) extends Regx
case class SEQ(r1: Regx, r2: Regx) extends Regx
case class ALT(r1: Regx, r2: Regx) extends Regx
case class STAR(r: Regx) extends Regx
 
def nullable(regx: Regx): Boolean = regx match {
  case ZERO        => false                            //Empty set
  case ONE         => true                             //Empty string
  case CHAR(c)     => false
  case SEQ(r1, r2) => nullable(r1) && nullable(r2)     //Sequence of 2 regexes
  case ALT(r1, r2) => nullable(r1) || nullable(r2)     //Alternative of 2 regexes
  case STAR(r)     => true                             //Star operation contains empty string
  }

def der(c: Char, regx: Regx): Regx = regx match {
  case ZERO        => ZERO
  case ONE         => ZERO
  case CHAR(d)     => if d == c ONE else ZERO
  case SEQ(r1, r2) => if nullable(r1) ALT( SEQ(der(c, r1), r2), der(c,r2) ) else SEQ(der(c, r1), r2)
  case ALT(r1, r2) => ALT( der(c, r1), der(c, r2) )
  case STAR(r)     => SEQ( der(c, r), STAR(r) )

}

def ders(s: List[Char], regx: Regx): Regx = s match{
  x::xs => ders( xs, der(x, regx) )
  Nil => regx
}

