// A Small Compiler for a Simple Functional Language
// (includes an external lexer and parser)
//
// call with
//
//     scala fun.scala fact
//
//     scala fun.scala defs
//
// this will generate a .j file and run the jasmin
// assembler (installed at jvm/jasmin-2.4/jasmin.jar)
// it runs the resulting JVM file twice for timing
// purposes.


import java.io._
import scala.util._
import scala.sys.process._
import scala.collection.mutable

import scala.language.implicitConversions
import scala.language.reflectiveCalls

abstract class Rexp
case object ZERO extends Rexp
case object ONE extends Rexp
case class CHAR(c: Char) extends Rexp
case class ALT(r1: Rexp, r2: Rexp) extends Rexp
case class SEQ(r1: Rexp, r2: Rexp) extends Rexp
case class STAR(r: Rexp) extends Rexp
case class RECD(x: String, r: Rexp) extends Rexp
case class RANGE(cs: List[Char]) extends Rexp // A list was used instead of a Set to improve readability when printing
case class PLUS(r: Rexp) extends Rexp
case class OPTIONAL(r: Rexp) extends Rexp
case class NTIMES(r: Rexp, n: Int) extends Rexp
case class CFUN(f: Char => Boolean) extends Rexp // For when using RANGE is not feasible/possible

abstract class Val
case object Empty extends Val
case class Chr(c: Char) extends Val
case class Sequ(v1: Val, v2: Val) extends Val
case class Left(v: Val) extends Val
case class Right(v: Val) extends Val
case class Stars(vs: List[Val]) extends Val
case class Rec(x: String, v: Val) extends Val
case class Rng(c: Char) extends Val
case class Plus(vs: List[Val]) extends Val
case class Optional(v: Val) extends Val
case class Ntimes(vs: List[Val]) extends Val // List of size n
case class Cfun(c: Char) extends Val

// some convenience for typing in regular expressions
def charlist2rexp(s : List[Char]): Rexp = s match {
  case Nil => ONE
  case c::Nil => CHAR(c)
  case c::s => SEQ(CHAR(c), charlist2rexp(s))
}
implicit def string2rexp(s : String) : Rexp =
  charlist2rexp(s.toList)

implicit def RexpOps(r: Rexp) = new {
  def | (s: Rexp) = ALT(r, s)
  def % = STAR(r)
  def ~ (s: Rexp) = SEQ(r, s)
  def + = PLUS(r)
  def ? = OPTIONAL(r)
  def ^ (n: Int) = NTIMES(r, n)
}

implicit def stringOps(s: String) = new {
  def | (r: Rexp) = ALT(s, r)
  def | (r: String) = ALT(s, r)
  def % = STAR(s)
  def ~ (r: Rexp) = SEQ(s, r)
  def ~ (r: String) = SEQ(s, r)
  def $ (r: Rexp) = RECD(s, r)
  def + = PLUS(s)
  def ? = OPTIONAL(s)
  def ^ (n: Int) = NTIMES(s, n)
}

// the nullable function: tests whether the regular
// expression can recognise the empty string
def nullable (r: Rexp) : Boolean = r match {
  case ZERO => false
  case ONE => true
  case CHAR(_) => false
  case ALT(r1, r2) => nullable(r1) || nullable(r2)
  case SEQ(r1, r2) => nullable(r1) && nullable(r2)
  case STAR(_) => true
  case RECD(_, r1) => nullable(r1)
  case RANGE(_) => false
  case PLUS(r) => nullable(r)
  case OPTIONAL(_) => true
  case NTIMES(r1, n) => if (n == 0) true else nullable(r1)
  case CFUN(_) => false
}

// the derivative of a regular expression w.r.t. a character
def der (c: Char, r: Rexp) : Rexp = r match {
  case ZERO => ZERO
  case ONE => ZERO
  case CHAR(d) => if (c == d) ONE else ZERO
  case ALT(r1, r2) => ALT(der(c, r1), der(c, r2))
  case SEQ(r1, r2) =>
    if (nullable(r1)) ALT(SEQ(der(c, r1), r2), der(c, r2))
    else SEQ(der(c, r1), r2)
  case STAR(r) => SEQ(der(c, r), STAR(r))
  case RECD(_, r1) => der(c, r1)
  case RANGE(s) => if (s.contains(c)) ONE else ZERO
  case PLUS(r1) => SEQ(der(c, r1), STAR(r1))
  case OPTIONAL(r1) => ALT(ZERO, der(c, r1))
  case NTIMES(r1, n) =>
    if (n == 0) ZERO
    else SEQ(der(c, r1), NTIMES(r1, n - 1))
  case CFUN(f) => if (f(c)) ONE else ZERO
}

// the derivative w.r.t. a string (iterates der)
@scala.annotation.tailrec
def ders(s: List[Char], r: Rexp) : Rexp = s match {
  case Nil => r
  case c::s => ders(s, der(c, r))
}

// extracts a string from value
def flatten(v: Val) : String = v match {
  case Empty => ""
  case Chr(c) => c.toString
  case Left(v) => flatten(v)
  case Right(v) => flatten(v)
  case Sequ(v1, v2) => flatten(v1) + flatten(v2)
  case Stars(vs) => vs.map(flatten).mkString
  case Rec(_, v) => flatten(v)
  case Rng(c) => c.toString
  case Plus(vs) => vs.map(flatten).mkString
  case Optional(v) => flatten(v)
  case Ntimes(vs) => vs.map(flatten).mkString
  case Cfun(c) => c.toString
}

// extracts an environment from a value;
// used for lexing a string
def env(v: Val) : List[(String, String)] = v match {
  case Empty => Nil
  case Chr(c) => Nil
  case Left(v) => env(v)
  case Right(v) => env(v)
  case Sequ(v1, v2) => env(v1) ::: env(v2)
  case Stars(vs) => vs.flatMap(env)
  case Rec(x, v) => (x, flatten(v))::env(v)
  case Rng(_) => Nil
  case Plus(vs) => vs.flatMap(env)
  case Optional(v) => env(v)
  case Ntimes(vs) => vs.flatMap(env)
  case Cfun(_) => Nil
}

// The Injection Part of the Lexer

// calculates a value for how a nullable regex
// matches the empty string
def mkeps(r: Rexp) : Val = r match {
  case ONE => Empty
  case ALT(r1, r2) =>
    if (nullable(r1)) Left(mkeps(r1)) else Right(mkeps(r2))
  case SEQ(r1, r2) => Sequ(mkeps(r1), mkeps(r2))
  case STAR(_) => Stars(Nil)
  case RECD(x, r) => Rec(x, mkeps(r))
  case PLUS(r1) => Plus(mkeps(r1) :: Nil) // Assume 1 time
  case OPTIONAL(r1) => Optional(Empty)
  case NTIMES(r1, n) =>
    if (n == 0) Ntimes(Nil)
    else Ntimes((for(_ <- 1 to n) yield mkeps(r1)).toList)
}

// injects back a character into a value
def inj(r: Rexp, c: Char, v: Val) : Val = (r, v) match {
  case (STAR(r), Sequ(v1, Stars(vs))) => Stars(inj(r, c, v1)::vs)
  case (SEQ(r1, r2), Sequ(v1, v2)) => Sequ(inj(r1, c, v1), v2)
  case (SEQ(r1, r2), Left(Sequ(v1, v2))) => Sequ(inj(r1, c, v1), v2)
  case (SEQ(r1, r2), Right(v2)) => Sequ(mkeps(r1), inj(r2, c, v2))
  case (ALT(r1, r2), Left(v1)) => Left(inj(r1, c, v1))
  case (ALT(r1, r2), Right(v2)) => Right(inj(r2, c, v2))
  case (CHAR(d), Empty) => Chr(c)
  case (RECD(x, r1), _) => Rec(x, inj(r1, c, v))
  case (RANGE(_), Empty) => Rng(c)
  case (PLUS(r1), Sequ(v1, Stars(vs))) => Plus(inj(r1, c, v1)::vs)
  case (OPTIONAL(r1), v1) => Optional(inj(r1, c, v1))
  case (NTIMES(r1, n), Sequ(v1, Ntimes(vs))) => Ntimes(inj(r1, c, v1)::vs)
  case (CFUN(_), Empty) => Cfun(c)
}

// a simple test for extracting an environment
//val re1 : Rexp = ("first" $ ("a" | "ab")) ~ ("second" $ ("b" | ONE))
//env(lexing(re1, "ab"))

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

def simp(r: Rexp): (Rexp, Val => Val) = r match {
  case ALT(r1, r2) => {
    val (r1s, f1s) = simp(r1)
    val (r2s, f2s) = simp(r2)
    (r1s, r2s) match {
      case (ZERO, _) => (r2s, F_RIGHT(f2s))
      case (_, ZERO) => (r1s, F_LEFT(f1s))
      case _ => if (r1s == r2s) (r1s, F_LEFT(f1s))
      else (ALT (r1s, r2s), F_ALT(f1s, f2s))
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
  case r => (r, F_ID)
}

// lexing functions including simplification
def lex_simp(r: Rexp, s: List[Char]) : Val = s match {
  case Nil => if (nullable(r)) mkeps(r) else
  { throw new Exception("lexing error") }
  case c::cs => {
    val (r_simp, f_simp) = simp(der(c, r))
    inj(r, c, f_simp(lex_simp(r_simp, cs)))
  }
}

def lexing_simp(r: Rexp, s: String) =
  env(lex_simp(r, s.toList))


// The Lexing Rules for a Small While Language

val LETTER = RANGE((('A' to 'Z') ++ ('a' to 'z')).toList)
val SYM = LETTER | "_"
val DIGIT_ZERO : Rexp = "0"
val DIGIT_NONZERO = RANGE(('1' to '9').toList)
val DIGIT = DIGIT_ZERO | DIGIT_NONZERO
val ID = LETTER ~ (SYM | DIGIT).%
val NUM = DIGIT_ZERO | DIGIT_NONZERO ~ DIGIT.%
val KEYWORD : Rexp = "skip" | "while" | "do" | "if" | "then" | "else" | "read" | "write" | "true" | "false" | "for" | "upto"
val SEMI: Rexp = ";"
val OP: Rexp = ":=" | "==" | "-" | "+" | "*" | "!=" | "<" | ">" | "<=" | ">=" | "%" | "/" | "&&" | "||"
val WHITESPACE = PLUS(" " | "\n" | "\t" | "\r\n") // Modified to include \r\n
val RPAREN: Rexp = ")"
val LPAREN: Rexp = "("
val BEGIN: Rexp = "{"
val END: Rexp = "}"
val PARENTHESES: Rexp = RPAREN | LPAREN | BEGIN | END
val STRING: Rexp = "\"" ~ CFUN((c: Char) => c != '"' ).% ~ "\""


val WHILE_REGS = (("k" $ KEYWORD) |
  ("i" $ ID) |
  ("o" $ OP) |
  ("n" $ NUM) |
  ("s" $ SEMI) |
  ("str" $ STRING) |
  ("p" $ PARENTHESES) |
  ("w" $ WHITESPACE)).%


// CW03 Start
abstract class Token
case object T_SEMI extends Token
case object T_LPAREN extends Token
case object T_RPAREN extends Token
case class T_ID(s: String) extends Token
case class T_OP(s: String) extends Token
case class T_NUM(n: Int) extends Token
case class T_KWD(s: String) extends Token
case class T_STR(s: String) extends Token
case object T_BEGIN extends Token
case object T_END extends Token


def paren2token(str: String) : Token = str match {
  case "(" => T_LPAREN
  case ")" => T_RPAREN
  case "{" => T_BEGIN
  case "}" => T_END
}

def stringPair2token(pair: (String, String)) : Token = pair match {
  case ("k", s) => T_KWD(s)
  case ("i", s) => T_ID(s)
  case ("o", s) => T_OP(s)
  case ("n", s) => T_NUM(s.toInt)
  case ("s", _) => T_SEMI
  case ("str", s) => T_STR(s.substring(1, s.length - 1)) //case ("str", s) => T_STR(s.replaceAll("\"", ""))
  case ("p", s) => paren2token(s)
}

def stringPairs2tokens(lst: List[(String, String)]) : List[Token] =
  for (pair <- lst; if pair._1 != "w") yield stringPair2token(pair) // Ignores whitespace


case class ~[+A, +B](_1: A, _2: B)


type IsSeq[A] = A => Seq[_]

abstract class Parser[I : IsSeq, T] {
  def parse(ts: I): Set[(T, I)]

  def parse_all(ts: I) : Set[T] =
    for ((head, tail) <- parse(ts); if tail.isEmpty) yield head
}

class SeqParser[I : IsSeq, T, S](p: => Parser[I, T], q: => Parser[I, S]) extends Parser[I, ~[T, S]] {
  def parse(sb: I) =
    for ((head1, tail1) <- p.parse(sb);
         (head2, tail2) <- q.parse(tail1)) yield (new ~(head1, head2), tail2)
}

class AltParser[I : IsSeq, T](p: => Parser[I, T], q: => Parser[I, T]) extends Parser[I, T] {
  def parse(sb: I) = p.parse(sb) ++ q.parse(sb)
}

class FunParser[I : IsSeq, T, S](p: => Parser[I, T], f: T => S) extends Parser[I, S] {
  def parse(sb: I) =
    for ((head, tail) <- p.parse(sb)) yield (f(head), tail)
}

case class TokenParser(tk: Token) extends Parser[List[Token], Token] {
  def parse(sb: List[Token]): Set[(Token, List[Token])] = sb match {
    case head::tail => if (head == tk) Set((tk, tail)) else Set()
    case _ => Set()
  }
}

case object StringParser extends Parser[List[Token], String] {
  def parse(sb: List[Token]): Set[(String, List[Token])] = sb match {
    case T_STR(s)::tail => Set((s, tail))
    case _ => Set()
  }
}

case object NumParser extends Parser[List[Token], Int] {
  def parse(sb: List[Token]): Set[(Int, List[Token])] = sb match {
    case T_NUM(n)::tail => Set((n, tail))
    case _ => Set()
  }
}


implicit def token2Parser(tk: Token) = TokenParser(tk)

implicit def ParserOps[I : IsSeq, T](p: Parser[I, T]) = new {
  def ||(q : => Parser[I, T]) = new AltParser[I, T](p, q)
  def ==>[S] (f: => T => S) = new FunParser[I, T, S](p, f)
  def ~[S](q : => Parser[I, S]) = new SeqParser[I, T, S](p, q)
}

implicit def TokenOps(tk: Token) = new {
  def ||(q : => Parser[List[Token], Token]) = new AltParser[List[Token], Token](tk, q)
  def ||(r: Token) = new AltParser[List[Token], Token](tk, r)
  def ==>[S] (f: => Token => S) = new FunParser[List[Token], Token, S](tk, f)
  def ~[S](q : => Parser[List[Token], S]) =
    new SeqParser[List[Token], Token, S](tk, q)
  def ~(r: Token) =
    new SeqParser[List[Token], Token, Token](tk, r)
}



abstract class Stmt
abstract class AExp
abstract class BExp

type Block = List[Stmt]

case object Skip extends Stmt
case class If(a: BExp, bl1: Block, bl2: Block) extends Stmt
case class While(b: BExp, bl: Block) extends Stmt
case class Assign(s: String, a: AExp) extends Stmt
case class Write(s: String) extends Stmt
case class WriteStr(s: String) extends Stmt

case class For(s: String, a1: AExp, a2: AExp, b: Block) extends Stmt


case class Read(s: String) extends Stmt
case class Var(s: String) extends AExp
case class Num(i: Int) extends AExp
case class Aop(o: String, a1: AExp, a2: AExp) extends AExp

case object True extends BExp
case object False extends BExp
case class Bop(o: String, a1: AExp, a2: AExp) extends BExp
case class And(b1: BExp, b2: BExp) extends BExp
case class Or(b1: BExp, b2: BExp) extends BExp

case object IDTokenParser extends Parser[List[Token], String] {
  def parse(sb: List[Token]): Set[(String, List[Token])] = sb match {
    case T_ID(name)::tail => Set((name, tail))
    case _ => Set()
  }
}

// arithmetic expressions
lazy val AExp: Parser[List[Token], AExp] =
  (Te ~ T_OP("+") ~ AExp) ==> { case x ~ _ ~ z => Aop("+", x, z): AExp } ||
    (Te ~ T_OP("-") ~ AExp) ==> { case x ~ _ ~ z => Aop("-", x, z): AExp } || Te
lazy val Te: Parser[List[Token], AExp] =
  (Fa ~ T_OP("*") ~ Te) ==> { case x ~ _ ~ z => Aop("*", x, z): AExp } ||
    (Fa ~ T_OP("/") ~ Te) ==> { case x ~ _ ~ z => Aop("/", x, z): AExp } ||
    (Fa ~ T_OP("%") ~ Te) ==> { case x ~ _ ~ z => Aop("%", x, z): AExp } || Fa
lazy val Fa: Parser[List[Token], AExp] =
  (T_LPAREN ~ AExp ~ T_RPAREN) ==> { case _ ~ y ~ _ => y } ||
    IDTokenParser ==> Var ||
    NumParser ==> Num

// boolean expressions with some simple nesting
lazy val BExp: Parser[List[Token], BExp] =
  (AExp ~ T_OP("==") ~ AExp) ==> { case x ~ _ ~ z => Bop("==", x, z): BExp } ||
    (AExp ~ T_OP("!=") ~ AExp) ==> { case x ~ _ ~ z => Bop("!=", x, z): BExp } ||
    (AExp ~ T_OP("<") ~ AExp) ==> { case x ~ _ ~ z => Bop("<", x, z): BExp } ||
    (AExp ~ T_OP(">") ~ AExp) ==> { case x ~ _ ~ z => Bop(">", x, z): BExp } ||
    (AExp ~ T_OP(">=") ~ AExp) ==> { case x ~ _ ~ z => Bop(">", x, z): BExp } ||
    (AExp ~ T_OP("<=") ~ AExp) ==> { case x ~ _ ~ z => Bop(">", x, z): BExp } ||
    (T_LPAREN ~ BExp ~ T_RPAREN ~ T_OP("&&") ~ BExp) ==> { case _ ~ y ~ _ ~ _ ~ v => And(y, v): BExp } ||
    (T_LPAREN ~ BExp ~ T_RPAREN ~ T_OP("||") ~ BExp) ==> { case _ ~ y ~ _ ~ _ ~ v => Or(y, v): BExp } ||
    (T_KWD("true") ==> (_ => True: BExp )) ||
    (T_KWD("false") ==> (_ => False: BExp )) ||
    (T_LPAREN ~ BExp ~ T_RPAREN) ==> { case _ ~ x ~ _ => x }

// statement / statements
lazy val Stmt: Parser[List[Token], Stmt] =
  ((T_KWD("skip") ==> (_ => Skip: Stmt)) ||
    (IDTokenParser ~ T_OP(":=") ~ AExp) ==> { case x ~ _ ~ z => Assign(x, z): Stmt } ||
    //(T_KWD("write") ~ T_LPAREN ~ IDTokenParser ~ T_RPAREN) ==> { case _ ~ _ ~ y ~ _ => Write(y): Stmt } ||
    (T_KWD("write") ~ IDTokenParser) ==> { case _ ~ y => Write(y): Stmt } ||
    (T_KWD("write") ~ StringParser) ==> { case _ ~ y => WriteStr(y): Stmt } ||
    (T_KWD("if") ~ BExp ~ T_KWD("then") ~ Block ~ T_KWD("else") ~ Block) ==>
      { case _ ~ y ~ _ ~ u ~ _ ~ w => If(y, u, w): Stmt } ||
    (T_KWD("while") ~ BExp ~ T_KWD("do") ~ Block) ==> { case _ ~ y ~ _ ~ w => While(y, w) } ||
    (T_KWD("read")  ~ IDTokenParser ==> {case _ ~ y => Read(y): Stmt}) ||
    (T_KWD("for") ~ IDTokenParser ~ T_OP(":=") ~ AExp ~ T_KWD("upto") ~ AExp ~ T_KWD("do") ~ Block ==>
      { case _ ~ id ~ _ ~ a1 ~ _ ~ a2 ~ _ ~ b => For(id, a1, a2, b)}))

lazy val Stmts: Parser[List[Token], Block] =
  (Stmt ~ T_SEMI ~ Stmts) ==> { case x ~ _ ~ z => x :: z : Block } ||
    (Stmt ==> ( s => List(s) : Block))

// blocks (enclosed in curly braces)
lazy val Block: Parser[List[Token], Block] =
  ((T_BEGIN ~ Stmts ~ T_END) ==> { case _ ~ y ~ _ => y } ||
    (Stmt ==> (s => List(s))))


// compiler - built-in functions
// copied from http://www.ceng.metu.edu.tr/courses/ceng444/link/jvm-cpm.html
//

val library = """
.class public XXX.XXX
.super java/lang/Object

.method public static write(I)V
        .limit locals 1
        .limit stack 2
        getstatic java/lang/System/out Ljava/io/PrintStream;
        iload 0
        invokevirtual java/io/PrintStream/println(I)V
        return
.end method

.method public static writes(Ljava/lang/String;)V
        .limit stack 2
        .limit locals 1
        getstatic java/lang/System/out Ljava/io/PrintStream;
        aload 0
        invokevirtual java/io/PrintStream/println(Ljava/lang/String;)V
        return
.end method

.method public static read()I
        .limit locals 10
        .limit stack 10

        ldc 0
        istore 1 ; this will hold our final integer
Label1:
        getstatic java/lang/System/in Ljava/io/InputStream;
        invokevirtual java/io/InputStream/read()I
        istore 2
        iload 2
        ldc 13 ; the newline delimiter for windows. Change to 10 for unix
        isub
        ifeq Label2
        iload 2
        ldc 32 ; the space delimiter
        isub
        ifeq Label2
        iload 2
        ldc 48 ; we have our digit in ASCII , have to subtract it from 48
        isub
        ldc 10
        iload 1
        imul
        iadd
        istore 1
        goto Label1
Label2:
        ;when we come here we have our integer computed in Local Variable 1
        iload 1
        ireturn
.end method

"""

// calculating the maximal needed stack size
def max_stack_block(b: Block): Int = b match {
  case head::tail => max_stack_stmt(head) + max_stack_block(tail)
  case Nil => 0
}

def max_stack_stmt(s: Stmt): Int = s match {
  case Skip => 0
  case If(a, b1, b2) => max_stack_bexp(a) + math.max(max_stack_block(b1), max_stack_block(b2))
  case While(a, b1) => max_stack_bexp(a) + max_stack_block(b1)
  case Assign(_, a) => max_stack_aexp(a)
  case Write(_) => 2
  case WriteStr(_) => 1
  case Read(_) => 10
  case For(_, a1, a2, b) => max_stack_aexp(a1) + max_stack_aexp(a2) + max_stack_block(b)
}

def max_stack_aexp(e: AExp): Int = e match {
  case Var(_) => 1
  case Num(_) => 1
  case Aop(_, a1, a2) => max_stack_aexp(a1) + max_stack_aexp(a2)
}

def max_stack_bexp(e: BExp): Int = e match {
  case True => 1
  case False => 1
  case Bop(_, a1, a2) => max_stack_aexp(a1) + max_stack_aexp(a2)
  case And(a1, a2) => max_stack_bexp(a1) + max_stack_bexp(a2)
  case Or(a1, a2) => max_stack_bexp(a1) + max_stack_bexp(a2)
}


// for generating new labels
var counter = -1

def Fresh(x: String) = {
  counter += 1
  x ++ "_" ++ counter.toString
}

var varIndexCounter = -1

def FreshVarIndex() : Int = {
  varIndexCounter += 1
  varIndexCounter
}

// CW04 Start
// convenient string interpolations
// for instructions, labels and methods
import scala.language.implicitConversions
import scala.language.reflectiveCalls

implicit def sring_inters(sc: StringContext) = new {
  def i(args: Any*): String = "   " ++ sc.s(args:_*) ++ "\n"
  def l(args: Any*): String = sc.s(args:_*) ++ ":\n"
  def m(args: Any*): String = sc.s(args:_*) ++ "\n"
}

implicit def make_env_mutable(m: collection.immutable.Map[String, Int]): mutable.Map[String, Int] =
  collection.mutable.Map(m.toSeq: _*)

type Env = collection.mutable.Map[String, Int]

// compile expressions
def compile_block(b: Block, env: Env) : String = b match {
  case head::tail => compile_stmt(head, env) + compile_block(tail, env)
  case Nil => ""
}

def compile_stmt(s: Stmt, env : Env) : String = s match {
  case Skip => ""
  case If(a, b1, b2) => {
    val if_else = Fresh("If_else")
    val if_end = Fresh("If_end")
    compile_bexp_with_jmp(a, env, if_else) ++ // Jump to the else branch if the expression is false
      compile_block(b1, env) ++ // The if body
      i"goto $if_end" ++ // Jump to the end
      l"$if_else" ++ // The label for the else branch
      compile_block(b2, env) ++ // The else body
      l"$if_end" // The label for the end of the if
  }
  case While(a, b1) => {
    val while_start = Fresh("While_start")
    val while_end = Fresh("While_end")
    l"$while_start" ++ // The start of while loop
      compile_bexp_with_jmp(a, env, while_end) ++ // Jump to the end if the condition is false
      compile_block(b1, env) ++ // The while loop body
      i"goto $while_start" ++ // Jump to the start of the while
      l"$while_end" // The end of while loop
  }
  case Assign(s, a) => {
    val indexOption = env.get(s)
    val varIndex = if (indexOption.isEmpty) FreshVarIndex() else indexOption.get
    env.addOne((s, varIndex))
    compile_aexp(a, env) ++ i"istore $varIndex"
  }
  case Write(s) => i"iload ${env(s)}" ++ i"invokestatic XXX/XXX/write(I)V"
  case WriteStr(s) => i"""ldc "$s"""" ++ i"invokestatic XXX/XXX/writes(Ljava/lang/String;)V"
  case Read(s) => {
    val varIndex = env.getOrElse(s, FreshVarIndex())
    env.addOne((s, varIndex))
    i"invokestatic XXX/XXX/read()I" ++ i"istore $varIndex"
  }
  case For(s, a1, a2, b) => {
    val for_start = Fresh("For_start")
    val for_end = Fresh("For_end")
    compile_stmt(Assign(s, a1), env) ++ // Initialise variable
      l"$for_start" ++ // The start of for loop
      compile_bexp_with_jmp(Bop("<=", Var(s), a2), env, for_end) ++ // Jump to the end if the variable is too large
      compile_block(b, env) ++ // The for loop body
      compile_stmt(Assign(s, Aop("+", Var(s), Num(1))), env) ++ // Increment the variable
      i"goto $for_start" ++ // Jump to the start
      l"$for_end" // The end of the for loop
  }
}

def compile_aexp(a: AExp, env: Env): String = a match {
  case Var(s) => i"iload ${env(s)}"
  case Num(n) => i"ldc $n" //TODO: Add specific constants
  case Aop(o, a1, a2) => o match {
    case "+" => compile_aexp(a1, env) ++ compile_aexp(a2, env) ++ i"iadd"
    case "-" => compile_aexp(a1, env) ++ compile_aexp(a2, env) ++ i"isub"
    case "*" => compile_aexp(a1, env) ++ compile_aexp(a2, env) ++ i"imul"
    case "/" => compile_aexp(a1, env) ++ compile_aexp(a2, env) ++ i"idiv"
    case "%" => compile_aexp(a1, env) ++ compile_aexp(a2, env) ++ i"irem"
  }
}

// compile boolean expressions
def compile_bexp_with_jmp(b: BExp, env : Env, jmp_label: String) : String = b match {
  case Bop("==", a1, a2) => compile_aexp(a1, env) ++ compile_aexp(a2, env) ++ i"if_icmpne $jmp_label"
  case Bop("!=", a1, a2) => compile_aexp(a1, env) ++ compile_aexp(a2, env) ++ i"if_icmpeq $jmp_label"
  case Bop("<", a1, a2) => compile_aexp(a1, env) ++ compile_aexp(a2, env) ++ i"if_icmpge $jmp_label"
  case Bop("<=", a1, a2) => compile_aexp(a1, env) ++ compile_aexp(a2, env) ++ i"if_icmpgt $jmp_label"
  case Bop(">", a1, a2) => compile_aexp(a1, env) ++ compile_aexp(a2, env) ++ i"if_icmple $jmp_label"
  case Bop(">=", a1, a2) => compile_aexp(a1, env) ++ compile_aexp(a2, env) ++ i"if_icmplt $jmp_label"
  case And(a1, a2) =>
    compile_bexp(a1, env) ++ compile_bexp(a2, env) ++ i"iand" ++ // 1 if result is true, 0 if not
      i"ifeq $jmp_label" // jumps if result is 0
  case Or(a1, a2) =>
    compile_bexp(a1, env) ++ compile_bexp(a2, env) ++ i"ior" ++ // 1 if result is true, 0 if not
      i"ifeq $jmp_label" // jumps if result is 0
  case True => i"goto $jmp_label"
  case False => ""
}

def compile_bexp(b: BExp, env: Env): String = b match {
  case And(a1, a2) =>
    compile_bexp(a1, env) ++ compile_bexp(a2, env) ++ i"iand"
  case Or(a1, a2) =>
    compile_bexp(a1, env) ++ compile_bexp(a2, env) ++ i"ior"
  case True => i"iconst_1"
  case False => i"iconst_0"
}

// compile function for declarations and main
def compile_main(b: Block) : String =
  m".method public static main([Ljava/lang/String;)V" ++
    m".limit locals 200" ++
    m".limit stack ${max_stack_block(b)}" ++
    compile_block(b, Map[String, Int]()) ++
    i"return" ++
    m".end method\n"

// Programs

val fib = """write "Fib";
            |read n;
            |minus1 := 0;
            |minus2 := 1;
            |while n > 0 do {
            |temp := minus2;
            |minus2 := minus1 + minus2;
            |minus1 := temp;
            |n := n - 1
            |};
            |write "Result";
            |write minus2""".stripMargin

val fact = """write "Fact";
            |read n;
            |result := 1;
            |while n > 1 do {
            |result := n * result;
            |n := n - 1
            |};
            |write "Result";
            |write result""".stripMargin

val loops = """for i := 1 upto 10 do {
              |for i := 1 upto 10 do {
              |write i
              |}
              |}""".stripMargin

val prog = loops

// main compiler functions

def time_needed[T](i: Int, code: => T) = {
  val start = System.nanoTime()
  for (j <- 1 to i) code
  val end = System.nanoTime()
  (end - start)/(i * 1.0e9)
}

def compile(class_name: String) : String = {
  val tokens = stringPairs2tokens(lexing_simp(WHILE_REGS, prog)) // Test fib
  val parseTree = Stmts.parse_all(tokens).head
  val instructions = compile_main(parseTree).mkString
  (library + instructions).replaceAllLiterally("XXX", class_name)
}

def compile_to_file(class_name: String) = {
  val output = compile(class_name)
  //scala.tools.nsc.io.File(s"${class_name}.j").writeAll(output)
  new PrintWriter(s"${class_name}.j") { write(output); close() }
}

def compile_and_run(class_name: String) : Unit = {
  compile_to_file(class_name)
  (s"java -jar jvm/jasmin-2.4/jasmin.jar ${class_name}.j").!!
  println("Time: " + time_needed(1, (s"java ${class_name}/${class_name}").!))
}


def main(args: Array[String]) : Unit = {
  //compile_and_run(args(0))
  compile_to_file(args(0))
}