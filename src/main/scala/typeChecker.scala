
sealed trait TypeError
case class TypeNotAFieldButAMethod(vl : String)           extends TypeError
case class TypeNotAMethodButAField(vl : String)           extends TypeError
case class TypeWrongNumberOfArguments(la : Int, lp : Int) extends TypeError
case class VariableExtrudesItsScope(x : String, ty : Type) extends TypeError
case class UndefinedVariable(x : String)                   extends TypeError


class Store {}  // TEMPORARY

trait TypeEnv {

  val body : Map[String, Type]

  def add(x : String, ty : Type) : TypeEnv =
    new TypeEnv { val body = TypeEnv.this.body + ((x, ty)) }


  def findVariable(x : String) : Option[Type] =
    body.get(x)

}

class EmptyTypeEnv extends TypeEnv {
  val body = Map()
}


object FWSTypeChecker {

  def typeCheck(store : Store, tyenv : TypeEnv, ast : Ast) : Either[TypeError, Type] =
    ast match {
      case Access(ast0, vlabel) =>
        pathOfAstIfPossible(ast0) match {
          case None =>
          /* -- if the expression 'ast0' is not (interprettable as) a path -- */
            typeCheck(store, tyenv, ast0) flatMap { ty0 =>
              membership(store, tyenv, ty0, vlabel) flatMap {
                case DeclVal(ty, _) =>
                  Right(ty)

                case DeclDef(_, _, _) =>
                  Left(TypeNotAFieldButAMethod(vlabel))
              }
            }

          case Some(path) =>
            val _ = typeCheckPath(store, tyenv, path);
            Right(SingletonType(path))
        }

      case Call(ast0, vlabel, astargs) =>
        typeCheck(store, tyenv, ast0) flatMap { ty0 =>
          membership(store, tyenv, ty0, vlabel) flatMap {
            case DeclVal(_, _) =>
              Left(TypeNotAMethodButAField(vlabel))

            case DeclDef(params, tyans, _) =>
              typeCheckParams(store, tyenv, params, astargs) flatMap { _ =>
                Right(tyans)
              }
          }
        }

      case Var(x) =>
        val path : Path = Path(x, Nil);
        typeCheckPath(store, tyenv, path) flatMap { _ =>
          Right(SingletonType(path))
        }

      case ValNewIn(x, ty, ast0) =>
        checkTypeWellFormedness(store, tyenv, ty) flatMap { _ =>
          typeCheck(store, tyenv.add(x, ty), ast0) flatMap { ty0 =>
            if (occursInType(x, ty0)) {
              Left(VariableExtrudesItsScope(x, ty0))
            } else {
              val phi : String = "(dummy)";
                /* -- a dummy variable name -- */
              expandType(store, tyenv, phi, ty) flatMap { _ =>
                Right(ty0)
              }
            }
          }
        }

    }


  def typeCheckParams(store : Store, tyenv : TypeEnv, params : List[(String, Type)], astargs : List[Ast]) : Either[TypeError, Unit] = {
    val lenArgs : Int = astargs.length;
    val lenParams : Int = params.length;
    if (lenArgs != lenParams) {
      Left(TypeWrongNumberOfArguments(lenArgs, lenParams))
    } else {
      val pairs : List[((String, Type), Ast)] = params.zip(astargs);
      val resInit : Either[TypeError, Unit] = Right(());
      pairs.foldLeft(resInit){ case (res, ((_, tyParam), astarg)) =>
        res flatMap { _ =>
          typeCheck(store, tyenv, astarg) flatMap { tyArg =>
            isSubtype(store, tyenv, tyArg, tyParam)
          }
        }
      }
    }
  }


  def occursInType(x : String, ty : Type) : Boolean =
    ???


  def expandType(store : Store, tyenv : TypeEnv, x : String, ty : Type) : Either[TypeError, List[Declaration]] =
    ???


  def checkTypeWellFormedness(store : Store, tyenv :TypeEnv, ty : Type) : Either[TypeError, Unit] =
    ???


  def isSubtype(store : Store, tyenv : TypeEnv, ty1 : Type, ty2 : Type) : Either[TypeError, Unit] =
    ???


  def pathOfAstIfPossible(ast : Ast) : Option[Path] = {
    def aux(vlabelacc : List[String], ast : Ast) : Option[Path] = {
      ast match {
        case Access(ast0, vlabel) =>
          aux(vlabel :: vlabelacc, ast0)

        case Var(x) =>
          Some(Path(x, vlabelacc.reverse))

        case _ =>
          None
      }
    };
    aux(Nil, ast)
  }


  def typeCheckPath(store : Store, tyenv : TypeEnv, path : Path) : Either[TypeError, Type] =
    path match { case Path(x, vlabels) =>
      vlabels.reverse match {
        case Nil =>
          tyenv.findVariable(x) match {
            case None     => Left(UndefinedVariable(x))
            case Some(ty) => Right(ty)
          }

        case vlabelLast :: vlabelRevTail =>
          membership(store, tyenv, SingletonType(Path(x, vlabelRevTail.reverse)), vlabelLast) flatMap {
            case DeclVal(ty, _)   => Right(ty)
            case DeclDef(_, _, _) => Left(TypeNotAFieldButAMethod(vlabelLast))
          }
      }
    }


  def membership(store : Store, tyenv : TypeEnv, ty : Type, vlabel : String) : Either[TypeError, ValueDeclBody] =
    ???
}
