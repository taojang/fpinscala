package fpinscala
package applicative

import monads.Functor
import state._
import State._
import StateUtil._ // defined at bottom of this file
import monoids._
import language.higherKinds
import language.implicitConversions

trait Applicative[F[_]] extends Functor[F] {

  def map2[A,B,C](fa: F[A], fb: F[B])(f: (A, B) => C): F[C] =
    apply((map(fa)(f.curried)))(fb)

  def apply[A,B](fab: F[A => B])(fa: F[A]): F[B] =
    map2(fab, fa)(_(_))

  def unit[A](a: => A): F[A]

  def map[A,B](fa: F[A])(f: A => B): F[B] =
    apply(unit(f))(fa)

  def sequence[A](fas: List[F[A]]): F[List[A]] =
    fas.foldLeft(unit(List.empty[A])) { case (fas, fa) =>
      map2(fa, fas)(_ :: _)
    }

  def traverse[A,B](as: List[A])(f: A => F[B]): F[List[B]] =
    as.foldLeft(unit(List.empty[B])) { case (fbs, a) =>
      map2(f(a), fbs)(_ :: _)
    }

  def replicateM[A](n: Int, fa: F[A]): F[List[A]] =
    sequence(List.fill(n)(fa))

  def factor[A,B](fa: F[A], fb: F[B]): F[(A,B)] =
    map2(fa, fb)(Tuple2.apply)

  def product[G[_]](G: Applicative[G]): Applicative[({type f[x] = (F[x], G[x])})#f] = {
    val self = this
    new Applicative[({type f[x] = (F[x], G[x])})#f] {
      def unit[A](a: => A) = (self.unit(a), G.unit(a))
      override def apply[A,B](fgab: (F[A => B], G[A => B]))(fga: (F[A], G[A])): (F[B], G[B]) =
        (self.apply(fgab._1)(fga._1), G.apply(fgab._2)(fga._2))
    }
  }

  def compose[G[_]](G: Applicative[G]): Applicative[({type f[x] = F[G[x]]})#f] = {
    val self = this
    new Applicative[({type f[x] = F[G[x]]})#f] {
      def unit[A](a: => A) = self.unit(G.unit(a))
      override def apply[A,B](fgab: F[G[A => B]])(fga: F[G[A]]): F[G[B]] =
        self.map2(fgab, fga)(G.apply(_)(_))
    }
  }

  def sequenceMap[K,V](ofa: Map[K,F[V]]): F[Map[K,V]] =
    map(sequence(ofa.toList.map { case (k, fv) =>
      factor(unit(k), fv)
    }))(kvs => Map.apply(kvs: _*))
}

case class Tree[+A](head: A, tail: List[Tree[A]])

trait Monad[F[_]] extends Applicative[F] {
  def flatMap[A,B](ma: F[A])(f: A => F[B]): F[B] = join(map(ma)(f))

  def join[A](mma: F[F[A]]): F[A] = flatMap(mma)(ma => ma)

  def compose[A,B,C](f: A => F[B], g: B => F[C]): A => F[C] =
    a => flatMap(f(a))(g)

  override def apply[A,B](mf: F[A => B])(ma: F[A]): F[B] =
    flatMap(mf)(f => map(ma)(a => f(a)))
}

object Monad {
  def eitherMonad[E]: Monad[({type f[x] = Either[E, x]})#f] = new Monad[({type f[x] = Either[E, x]})#f] {
    def unit[A](a: => A): Either[E, A] = Right(a)
    override def join[A](mma: Either[E, Either[E, A]]): Either[E, A] =
      mma match {
        case Left(e)         => Left(e)
        case Right(Left(e))  => Left(e)
        case Right(Right(a)) => Right(a)
      }
  }

  def stateMonad[S] = new Monad[({type f[x] = State[S, x]})#f] {
    def unit[A](a: => A): State[S, A] = State(s => (a, s))
    override def flatMap[A,B](st: State[S, A])(f: A => State[S, B]): State[S, B] =
      st flatMap f
  }

  def composeM[F[_],N[_]](implicit F: Monad[F], N: Monad[N], T: Traverse[N]): Monad[({type f[x] = F[N[x]]})#f] = new Monad[({type f[x] = F[N[x]]})#f] {
    def unit[A](a: => A): F[N[A]] = F.unit(N.unit(a))
    override def join[A](mma: F[N[F[N[A]]]]): F[N[A]] =
      F.join(F.map(mma)(nfna => F.map(T.sequence(nfna))(N.join)))
  }
}

sealed trait Validation[+E, +A]

case class Failure[E](head: E, tail: Vector[E])
  extends Validation[E, Nothing]

case class Success[A](a: A) extends Validation[Nothing, A]


object Applicative {

  val streamApplicative = new Applicative[Stream] {

    def unit[A](a: => A): Stream[A] =
      Stream.continually(a) // The infinite, constant stream

    override def map2[A,B,C](a: Stream[A], b: Stream[B])( // Combine elements pointwise
                    f: (A,B) => C): Stream[C] =
      a zip b map f.tupled
  }

  def validationApplicative[E]: Applicative[({type f[x] = Validation[E,x]})#f] = new Applicative[({type f[x] = Validation[E,x]})#f] {
    def unit[A](a: => A): Validation[E, A] = Success(a)
    override def apply[A,B](fab: Validation[E, A => B])(fa: Validation[E, A]): Validation[E, B] = (fab, fa) match {
      case (Failure(h, t), Failure(h1, t1)) =>
        Failure(h, t ++ (h1 +: t1))
      case (Failure(h, t), _) =>
        Failure(h, t)
      case (_, Failure(h, t)) =>
        Failure(h, t)
      case (Success(f), Success(a)) =>
        Success(f(a))
    }
  }

  type Const[A, B] = A

  implicit def monoidApplicative[M](M: Monoid[M]) =
    new Applicative[({ type f[x] = Const[M, x] })#f] {
      def unit[A](a: => A): M = M.zero
      override def apply[A,B](m1: M)(m2: M): M = M.op(m1, m2)
    }
}

trait Traverse[F[_]] extends Functor[F] with Foldable[F] {
  def traverse[G[_]:Applicative,A,B](fa: F[A])(f: A => G[B]): G[F[B]] =
    sequence(map(fa)(f))
  def sequence[G[_]:Applicative,A](fma: F[G[A]]): G[F[A]] =
    traverse(fma)(ma => ma)

  type Id[A] = A
  val idMonad = new Monad[Id] {
    def unit[A](a: => A) = a
    override def flatMap[A,B](a: A)(f: A => B): B = f(a)
  }

  def map[A,B](fa: F[A])(f: A => B): F[B] =
    traverse[Id, A, B](fa)(f)(idMonad)

  import Applicative._

  override def foldMap[A,B](as: F[A])(f: A => B)(mb: Monoid[B]): B =
    traverse[({type f[x] = Const[B,x]})#f,A,Nothing](
      as)(f)(monoidApplicative(mb))

  def traverseS[S,A,B](fa: F[A])(f: A => State[S, B]): State[S, F[B]] =
    traverse[({type f[x] = State[S,x]})#f,A,B](fa)(f)(Monad.stateMonad)

  def mapAccum[S,A,B](fa: F[A], s: S)(f: (A, S) => (B, S)): (F[B], S) =
    traverseS(fa)((a: A) => (for {
      s1 <- get[S]
      (b, s2) = f(a, s1)
      _  <- set(s2)
    } yield b)).run(s)

  override def toList[A](fa: F[A]): List[A] =
    mapAccum(fa, List[A]())((a, s) => ((), a :: s))._2.reverse

  def zipWithIndex[A](fa: F[A]): F[(A, Int)] =
    mapAccum(fa, 0)((a, s) => ((a, s), s + 1))._1

  def reverse[A](fa: F[A]): F[A] =
    mapAccum(fa, toList(fa).reverse)((_, as) => (as.head, as.tail))._1

  override def foldLeft[A,B](fa: F[A])(z: B)(f: (B, A) => B): B =
    mapAccum(fa, z)((a, b) => ((), f(b, a)))._2

  def fuse[G[_],H[_],A,B](fa: F[A])(f: A => G[B], g: A => H[B])
    (implicit G: Applicative[G], H: Applicative[H]): (G[F[B]], H[F[B]]) =
    traverse[({type f[x] = (G[x], H[x])})#f, A, B](fa)(a => (f(a), g(a)))(G.product(H))


  def compose[G[_]](implicit G: Traverse[G]): Traverse[({type f[x] = F[G[x]]})#f] = {
    val self = this
    new Traverse[({type f[x] = F[G[x]]})#f] {
      override def sequence[H[_],A](fgha: F[G[H[A]]])
        (implicit H: Applicative[H]): H[F[G[A]]] =
        self.sequence(self.map(fgha)(G.sequence(_)))
    }
  }
}

object Traverse {
  val listTraverse = new Traverse[List] {
    override def sequence[G[_],A](fma: List[G[A]])(implicit G: Applicative[G]): G[List[A]] =
      fma.foldRight(G.unit(List.empty[A])) { case (curr, acc) =>
        G.map2(curr, acc)(_ :: _)
      }
  }

  val optionTraverse = new Traverse[Option] {
    override def sequence[G[_], A](fma: Option[G[A]])(implicit G: Applicative[G]): G[Option[A]] =
      fma match {
        case Some(ga) => G.map(ga)(Some(_))
        case None => G.unit(None)
      }
  }

  val treeTraverse = new Traverse[Tree] {
    override def sequence[G[_], A](fma: Tree[G[A]])(implicit G: Applicative[G]): G[Tree[A]] =
      G.map2(fma.head, listTraverse.traverse(fma.tail)(sequence(_)))(Tree(_, _))
  }
}

// The `get` and `set` functions on `State` are used above,
// but aren't in the `exercises` subproject, so we include
// them here
object StateUtil {

  def get[S]: State[S, S] =
    State(s => (s, s))

  def set[S](s: S): State[S, Unit] =
    State(_ => ((), s))
}
