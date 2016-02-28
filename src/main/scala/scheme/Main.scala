package scheme

import cats._
import cats.data.{State, Xor}
import cats.std.all._
import cats.syntax.all._

import scala.annotation.tailrec
import scala.io.StdIn
import scala.util.parsing.combinator.JavaTokenParsers
import scala.util.{Failure, Success, Try}
import scala.{List => _}

object Scheme {
  type ThrowsError[A] = Xor[LispError, A]

  sealed abstract class Val
  case class Atom(name: String) extends Val
  case class List(contents: Vector[Val]) extends Val
  case class DottedList(head: Vector[Val], tail: Val) extends Val
  case class Number(contends: Int) extends Val
  case class Str(contents: String) extends Val
  case class Bool(contents: Boolean) extends Val
  case class PrimitiveFunc(func: Vector[Val] => ThrowsError[Val]) extends Val
  case class Func(params: Vector[String], varargs: Option[String], body: Vector[Val], closure: Env) extends Val

  type Env = Map[String, Val]
  type EnvThrowsError[A] = State[Env, ThrowsError[A]]
  val nullEnv: Env = Map()

  implicit object ShowVal extends Show[Val] {
    override def show(lispVal: Val): String = lispVal match {
      case Atom(name) => name
      case Str(contents) => "\"" + contents.show + "\""
      case Number(contents) => contents.show
      case Bool(true) => "#t"
      case Bool(false) => "#f"
      case List(contents) => "(" + contents.map(show).mkString(" ") + ")"
      case DottedList(head, tail) => "(" ++ head.map(show).mkString(" ") ++ " . " + show(tail) + ")"
      case PrimitiveFunc(_) => "<primitive>"
      case Func(args, varargs, body, closure) =>
        s"(lambda (${args.map(_.show).mkString(" ")}" ++
          varargs.map(" . " + _).getOrElse("") + ") ...)"
    }
  }

  sealed abstract class LispError
  case class NumArgs(expected: Int, found: Vector[Val]) extends LispError
  case class TypeMismatch(expected: String, found: Val) extends LispError
  case class ParserError(message: String) extends LispError
  case class BadSpecialForm(expected: String, found: Val) extends LispError
  case class NotFunction(message: String, func: String) extends LispError
  case class UnboundVar(message: String, varname: String) extends LispError
  case class DefaultError(message: String) extends LispError

  implicit object ShowLispError extends Show[LispError] {
    override def show(lispError: LispError): String = lispError match {
      case NumArgs(expected, found) => s"Expected $expected args: found values ${found.map(_.show).mkString(" ")}"
      case TypeMismatch(expected, found) => s"Invalid type: expected $expected, found: ${found.show}"
      case ParserError(message) => s"Parse error at $message"
      case BadSpecialForm(message, form: Val) => s"$message:${form.show}"
      case NotFunction(message, func) => s"$message: ${func.show}"
      case UnboundVar(message, varname) => s"$message: $varname "
      case DefaultError(message: String) => message
    }
  }

  def eval(in: Val): State[Env, ThrowsError[Val]] = in match {
    case Str(_) | Number(_) | Bool(_) => State(env => (env, in.right))
    case Atom(id) => getVar(id)
    case List(Vector(Atom("quote"), value)) => State(env => (env, value.right))
    case List(Vector(Atom("if"), pred, conseq, alt)) => eval(pred).flatMap({
      case Xor.Right(Bool(false)) => eval(alt)
      case _ => eval(conseq)
    })
    case List(Vector(Atom("set!"), Atom(varname), form)) =>
      eval(form).flatMap {
        case Xor.Right(lispVal) => State(env => (setVar(env, varname, lispVal), lispVal.right))
        case err => State(env => (env, err))
      }
    case List(Vector(Atom("define"), Atom(varname), form)) =>
      eval(form).flatMap {
        case Xor.Right(lispVal) => defineVar(varname, lispVal)
        case err => State(env => (env, err))
      }
    case List(Atom("define") +: List(Atom(varname) +: params) +: body) =>
      State { env =>
        val func = makeNormalFunc(env, params.map(_.show), body)
        (setVar(env, varname, func), func.right)
      }

    case List(Atom("define") +: DottedList(Atom(varname) +: params, varargs) +: body) =>
      State { env =>
        val func = makeVarargsFunc(env, varargs.show.some, params.map(_.show), body)
        (setVar(env, varname, func), func.right)
      }
    case List(Atom("lambda") +: List(params) +: body) =>
      State { env =>
        (env, makeNormalFunc(env, params.map(_.show), body).right)
      }
    case List(Atom("lambda") +: DottedList(params, varargs) +: body) =>
      State { env =>
        (env, makeVarargsFunc(env, varargs.show.some, params.map(_.show), body).right)
      }
    case List(Atom("lambda") +: (varargs@Atom(_)) +: body) =>
      State { env =>
        (env, makeVarargsFunc(env, varargs.name.some, Vector(), body).right)
      }

    case List(Atom(func) +: args) =>
      val list: State[Env, ThrowsError[Vector[Val]]] = sequenceT(args map eval)
      list.flatMap {
        case Xor.Right(xs) => getVar(func).flatMap {
          case Xor.Right(f) => apply(f)(args)
          case err@Xor.Left(_) => State(env => (env, err))
        }
        case err@Xor.Left(_) => State(env => (env, err))
      }
  }

  def apply: Val => Vector[Val] => State[Env, ThrowsError[Val]] = {
    case PrimitiveFunc(func) =>
      args =>
        State{env =>
           val as: ThrowsError[Vector[Val]] = sequence(args.map(v => eval(v).run(env).value._2))
          (env, as flatMap func) }
    case Func(params, varargs, body, closure) =>
      args =>
        val remainArgs = args.drop(params.length)

        def evalBody(env: Env): (Env, ThrowsError[Val]) = {
          body.map(input => eval(input).run(env).value).last
        }

        def bindVarArgs(arg: Option[String], env: Env): Env =
          arg.map { argname =>
            bindVars(env, Vector(argname -> List(remainArgs)))
          }.getOrElse(env)

        State { env =>
          val as: ThrowsError[Vector[Val]] = sequence(args.map(v => eval(v).run(env).value._2))
          as match {
            case Xor.Right(xs) =>
              val env1: Map[String, Val] = bindVarArgs(varargs, bindVars(bindVars(env, params zip args), closure.toVector))

              if (params.length != args.length && varargs.isEmpty) (env, NumArgs(params.length, args).left)
              else evalBody(env1)
            case err@Xor.Left(_) => (env, err)
          }
        }
    case notFunction =>
      args => State{env => (env, NotFunction("Not function", notFunction.show).left)}
  }

  val primitives: Map[String, Vector[Val] => ThrowsError[Val]] =
    Map(
      "+" -> numericBinop(_ + _),
      "-" -> numericBinop(_ - _),
      "*" -> numericBinop(_ * _),
      "/" -> numericBinop(_ / _),
      "mod" -> numericBinop(_ % _),
      "quotient" -> numericBinop(_ / _),
      "remainder" -> numericBinop((_: Int) - (_: Int)),
      "=" -> numBoolBinop(_ == _),
      "<" -> numBoolBinop(_ < _),
      ">" -> numBoolBinop(_ > _),
      "/=" -> numBoolBinop(_ != _),
      ">=" -> numBoolBinop(_ >= _),
      "<=" -> numBoolBinop(_ <= _),
      "&&" -> boolBoolBinop(_ && _),
      "||" -> boolBoolBinop(_ || _),
      "string=?" -> strBoolBinop(_ == _),
      //      "string?" -> strBoolBinop(_.isInstanceOf[String]), error
      "string<=?" -> strBoolBinop(_ <= _),
      "string>=?" -> strBoolBinop(_ >= _),
      "car" -> car,
      "cdr" -> cdr,
      "cons" -> cons,
      "eq?" -> eqv,
      "eqv?" -> eqv)

  private def sequence[A](nums: Vector[ThrowsError[A]]): ThrowsError[Vector[A]] =
    nums.foldLeft(Vector.empty[A].right: ThrowsError[Vector[A]]) {
      case (left@Xor.Left(_), _) => left
      case (_, left@Xor.Left(_)) => left
      case (Xor.Right(v), Xor.Right(x)) => v.:+(x).right
    }

  private def sequenceT[A](nums: Vector[State[Env, ThrowsError[A]]]): State[Env, ThrowsError[Vector[A]]] =
    nums.foldLeft(State(env => (env, Vector.empty[A].right)): EnvThrowsError[Vector[A]]) { (s1, s2) =>
      for {a1 <- s1; a2 <- s2}
        yield {
          for (xs <- a1; x <- a2) yield xs :+ x
        }
    }

  def numericBinop(f: (Int, Int) => Int): Vector[Val] => ThrowsError[Val] = {
    case args =>
      if (args.length == 1) NumArgs(2, args).left
      else {
        val nums: Vector[ThrowsError[Int]] = args map unpackNum
        val b: ThrowsError[Vector[Int]] = sequence(nums)
        b.map(_.reduce(f)).map(Number)
      }
  }

  private def unpackNum(in: Val): ThrowsError[Int] = in match {
    case Number(n) => n.right // right(n)
    case Str(n) =>
      Try(n.toInt) match {
        case Success(x) => x.right
        case Failure(e) => TypeMismatch("number", in).left
      }
    case List(Vector(x)) => unpackNum(x)
    case _ => TypeMismatch("number", in).left
  }

  type BoolBinop[A] = ((A, A) => Boolean) => Vector[Val] => ThrowsError[Val]

  def boolBinop[A]: (Val => ThrowsError[A]) => BoolBinop[A] =
    unpacker => op => args =>
      if (args.length != 2) NumArgs(2, args).left
      else for {left <- unpacker(args.head)
                right <- unpacker(args.last)}
        yield Bool(op(left, right))

  def numBoolBinop: BoolBinop[Int] = boolBinop(unpackNum)

  def strBoolBinop: BoolBinop[String] = boolBinop(unpackStr)

  def boolBoolBinop: BoolBinop[Boolean] = boolBinop(unpackBool)

  def unpackStr: Val => ThrowsError[String] = {
    case Str(s) => s.right
    case Number(s) => s.show.right
    case Bool(s) => s.show.right
    case notString => TypeMismatch("string", notString).left
  }

  def unpackBool: Val => ThrowsError[Boolean] = {
    case Bool(b) => b.right
    case notBool => TypeMismatch("boolean", notBool).left
  }

  def car: Vector[Val] => ThrowsError[Val] = {
    case Vector(List(x +: _)) => x.right
    case Vector(DottedList(x +: _, _)) => x.right
    case Vector(badArg) => TypeMismatch("pair", badArg).left
    case badArgList => NumArgs(1, badArgList).left
  }

  def cdr: Vector[Val] => ThrowsError[Val] = {
    case Vector(List(_ +: xs)) => List(xs).right
    case Vector(DottedList(_ +: xs, x)) => DottedList(xs, x).right
    case Vector(DottedList(_, x)) => x.right
    case Vector(badArg) => TypeMismatch("pair", badArg).left
    case badArgList => NumArgs(1, badArgList).left
  }

  def cons: Vector[Val] => ThrowsError[Val] = {
    case Vector(x1, List(Vector())) => List(Vector(x1)).right
    case Vector(x, List(xs)) => List(x +: xs).right
    case Vector(x, DottedList(xs, xlast)) => DottedList(x +: xs, xlast).right
    case Vector(x1, x2) => DottedList(Vector(x1), x2).right
    case badArgList => NumArgs(2, badArgList).left
  }

  def eqv: Vector[Val] => ThrowsError[Val] = {
    case Vector(Bool(x), Bool(y)) => Bool(x == y).right
    case Vector(Number(x), Number(y)) => Bool(x == y).right
    case Vector(Str(x), Str(y)) => Bool(x == y).right
    case Vector(Atom(x), Atom(y)) => Bool(x == y).right
    case Vector(DottedList(xs, x), DottedList(ys, y)) => eqv(Vector(List(xs :+ x), List(ys :+ y)))
    case Vector(List(xs), List(ys)) =>
      Bool((xs.length == ys.length) &&
        xs.zip(ys).forall { case (x, y) => eqv(Vector(x, y)) == Bool(true).right }).right
    case Vector(_, _) => Bool(false).right
    case badArgList => NumArgs(2, badArgList).left
  }

  object LispParser extends JavaTokenParsers {
    override def skipWhitespace: Boolean = false

    private def oneOf(s: String): Parser[Char] = s.toList.map(accept).reduce(_ | _)

    private def letter: Parser[Char] = acceptIf(_.isLetter)(_.toString)

    private def digit: Parser[Char] = acceptIf(_.isDigit)(_.toString)

    def symbol: Parser[Char] = oneOf("!$%&|*+-/:<=?>@^_~#")

    def spaces: Parser[Unit] = whiteSpace ^^ { _ => () }

    def expr: Parser[Val] = opt(spaces) ~>
      (atom | string | number | quoted | "(" ~> list <~ ")" | "(" ~> dottedList <~ ")")

    def string: Parser[Val] = stringLiteral ^^ { s => Str(s.tail.init) }

    def atom: Parser[Val] = (letter | symbol) ~ rep(letter | digit | symbol) ^^ {
      case first ~ rest =>
        val atom = (first :: rest).mkString
        atom match {
          case "#t" => Bool(true)
          case "#f" => Bool(false)
          case _ => Atom(atom)
        }
    }

    def number: Parser[Val] = wholeNumber ^^ { a => Number(a.toInt) }

    def list: Parser[Val] = repsep(expr, spaces) ^^ { case xs => List(xs.toVector) }

    def dottedList: Parser[Val] = repsep(expr, spaces) ~ (spaces ~ "." ~ spaces) ~ expr ^^ {
      case head ~ _ ~ tail => DottedList(head.toVector, tail)
    }

    def quoted: Parser[Val] = "\'" ~> expr ^^ { x => List(Vector(Atom("quote"), x)) }
  }

  def isBound(varname: String): State[Env, Boolean] = State { env =>
    (env, env.contains(varname))
  }

  def getVar(varname: String): State[Env, ThrowsError[Val]] = State(env => env.get(varname) match {
    case None => (env, UnboundVar("Getting an unbound variable" + env.toString(), varname).left)
    case Some(x) => (env, x.right)
  })

  def setVar(env: Env, varname: String, x: Val): Env =
    env + (varname -> x)

  def defineVar(varname: String, x: Val): State[Env, ThrowsError[Val]] =
    State(env => (env + (varname -> x), x.right))

  def bindVars(env: Env, bindings: Vector[(String, Val)]): Env =
    env ++ bindings

  def primitiveBindings: Env = {
    def makePrimitiveFunc(varname: String, func: Vector[Val] => ThrowsError[Val]) =
      varname -> PrimitiveFunc(func)

    primitives.map((makePrimitiveFunc _).tupled)
  }

  def makeNormalFunc(env: Env, params: Vector[String], body: Vector[Val]): Func =
    Func(params, None, body, env)

  def makeVarargsFunc(env: Env, vararg: Option[String], params: Vector[String], body: Vector[Val]): Func =
    Func(params, vararg, body, env)
}

object Main {

  import Scheme._
  import LispParser._

  def readExpr(input: String): Val = {
    LispParser.parse(LispParser.expr, input) match {
      case LispParser.Success(lispVal, _) => lispVal
      case Error(msg, in) => Str(msg)
      case LispParser.Failure(msg, in) => Str(msg)
    }
  }

  def showValue[A: Show](ta: ThrowsError[A]): String = ta match {
    case Xor.Right(a) => a.show
    case Xor.Left(err) => s"ERROR: ${err.show}"
  }

  def main(args: Array[String]): Unit = {
    @tailrec
    def repl(env: Env): Unit ={
      val input = StdIn.readLine("lisp>>")
      if (input != "quite") {
        val (env1, v) = eval(readExpr(input)).run(env).value
        println(showValue(v))
        repl(env1)
      }
    }
    repl(primitiveBindings)
  }
}