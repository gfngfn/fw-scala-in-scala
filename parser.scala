import scala.util.parsing.combinator._


sealed abstract class Ast
case class ValNewIn(x : String, ty : Type, e : Ast)   extends Ast
case class Var(x : String)                            extends Ast
case class Access(e : Ast, vl : String)               extends Ast
case class Call(e : Ast, vl : String, es : List[Ast]) extends Ast


class Path(x : String, vls : List[String])
object Path {
  def apply(x : String, vls : List[String]) =
    new Path(x, vls)
}


class Intersection(tys : List[Type], x : String, decls : List[Declaration])
object Intersection {
  def apply(tys : List[Type], x : String, decls : List[Declaration]) =
    new Intersection(tys, x, decls)
}


sealed abstract class Type
case class TypeSelection(p : Path, tl : String) extends Type
case class SingletonType(sty : Path)            extends Type
case class TypeSignature(tysig : Intersection)  extends Type


sealed abstract class Declaration
case class DeclVal(vl : String, ty : Type, eopt : Option[Ast]) extends Declaration
case class DeclDef(vl : String, params : List[(String, Type)], tyans : Type, eopt : Option[Ast]) extends Declaration
case class DeclType(tl : String, tyopt : Option[Type]) extends Declaration
case class DeclTrait(tl : String, tysig : Intersection) extends Declaration


object FWSParser extends JavaTokenParsers {

  val reservedWord = List("val", "def", "new", "type", "trait")

  def variable : Parser[String] =
    ident ^? {
      case s if (!(reservedWord.contains(s))) => s
    }

  def valueLabel :Parser[String] = ident
  def typeLabel : Parser[String] = ident

  def expr : Parser[Ast] =
    ( "val" ~> ((variable <~ "=") <~ "new") ~ (typ <~ ";") ~ expr ^^ {
        case x ~ ty ~ e => ValNewIn(x, ty, e)
      }
    | exprChain
    )

  def exprChain : Parser[Ast] =
    variable ~ rep("." ~> valueLabel ~ opt(args)) ^^ {
      case x ~ lst =>
        val init : Ast = Var(x);
        lst.foldLeft(init)((eacc, pair) =>
          pair match {
            case vl ~ None     => Access(eacc, vl)
            case vl ~ Some(es) => Call(eacc, vl, es)
          }
        )
    }

  def args : Parser[List[Ast]] =
    "(" ~> (opt(rep1sep(expr, ",")) <~ ")") ^^ {
      case None     => Nil
      case Some(es) => es
    }

  def params : Parser[List[(String, Type)]] =
    "(" ~> (opt(rep1sep((variable <~ ":") ~ typ, ",")) <~ ")") ^^ {
      case None      => Nil
      case Some(lst) => lst.map({ case e ~ ty => (e, ty)})
    }

  def typ : Parser[Type] =
    ( singletonType
    | typeSignature ^^ {
        case tysig => TypeSignature(tysig)
      }
    | (path <~ ".") ~ typeLabel ^^ {
        case p ~ tl => TypeSelection(p, tl)
      }
    )

  def singletonType : Parser[Type] =
    path <~ ".type" ^^ {
      case p => SingletonType(p)
    }

  def typeSignature : Parser[Intersection] =
    "(" ~> ((rep1sep(typ, ",") <~ ")") <~ "{") ~ (variable <~ "|") ~ (rep(decl) <~ "}") ^^ {
      case tys ~ x ~ decls => Intersection(tys, x, decls)
    }

  def decl : Parser[Declaration] =
    ( "val" ~> (valueLabel <~ ":") ~ typ ~ opt("=" ~> expr) ^^ {
        case vl ~ ty ~ eopt => DeclVal(vl, ty, eopt)
      }
    | "def" ~> valueLabel ~ (params <~ ":") ~ typ ~ opt("=" ~> expr) ^^ {
        case vl ~ pars ~ ty ~ eopt => DeclDef(vl, pars, ty, eopt)
      }
    | "type" ~> typeLabel ~ opt("=" ~> typ) ^^ {
        case tl ~ tyopt => DeclType(tl, tyopt)
      }
    | "trait" ~> typeLabel ~ typeSignature ^^ {
        case tl ~ tysig => DeclTrait(tl, tysig)
      }
    )

  def path : Parser[Path] =
    variable ~ rep("." ~> valueLabel) ^^ {
      case x ~ vls => Path(x, vls)
    }

}
