{-# LANGUAGE EmptyDataDecls, ExistentialQuantification,
  ScopedTypeVariables, NoMonomorphismRestriction, Rank2Types #-}
module MAlonzo.Code.Category.Monad.Indexed where
import MAlonzo.RTE (coe, erased)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Category.Applicative.Indexed
import qualified MAlonzo.Code.Function
import qualified MAlonzo.Code.Level
name14 = "Category.Monad.Indexed.RawIMonad"
d14 a0 a1 a2 a3 = ()

data T14 a0 a1 = C1 a0 a1
name46 = "Category.Monad.Indexed.RawIMonad.return"
d46 v0
  = case coe v0 of
        C1 v1 v2 -> coe v1
        _ -> coe MAlonzo.RTE.mazUnreachableError
name58 = "Category.Monad.Indexed.RawIMonad._>>=_"
d58 v0
  = case coe v0 of
        C1 v1 v2 -> coe v2
        _ -> coe MAlonzo.RTE.mazUnreachableError
name70 = "Category.Monad.Indexed.RawIMonad._>>_"
d70 v0 v1 v2 v3 v4 v5 v6 v7
  = coe d58 v0 v1 v2 v3 v4 v5 v6 (\ v8 -> v7)
name88 = "Category.Monad.Indexed.RawIMonad._=<<_"
d88 v0 v1 v2 v3 v4 v5 v6 v7 = coe d58 v0 v1 v2 v3 v4 v5 v7 v6
name108 = "Category.Monad.Indexed.RawIMonad._>=>_"
d108 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13
  = du108 v4 v5 v6 v7 v10 v11 v12 v13
du108 v0 v1 v2 v3 v4 v5 v6 v7
  = coe MAlonzo.Code.Function.d38 erased erased erased erased erased
      erased
      (\ v8 v9 -> coe d58 v0 v1 v2 v3 v4 v5 v9 v7)
      v6
name128 = "Category.Monad.Indexed.RawIMonad._<=<_"
d128 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13
  = du128 v4 v5 v6 v7 v8 v9 v12 v13
du128 v0 v1 v2 v3 v4 v5 v6 v7 = coe du108 v0 v1 v2 v3 v4 v5 v7 v6
name142 = "Category.Monad.Indexed.RawIMonad.join"
d142 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 = du142 v3 v4 v5 v6 v7 v8 v9
du142 v0 v1 v2 v3 v4 v5 v6
  = coe d58 v1 v2 v3 v4 (coe v0 v3 v4 v5) v5 v6
      (coe MAlonzo.Code.Function.d68 erased erased)
name146 = "Category.Monad.Indexed.RawIMonad.rawIApplicative"
d146 v0 v1 v2 v3 v4 = du146 v4
du146 v0
  = coe MAlonzo.Code.Category.Applicative.Indexed.C9 (coe d46 v0)
      (\ v1 v2 v3 v4 v5 v6 v7 ->
         coe d58 v0 v1 v2 v3 () v5 v6
           (\ v8 ->
              coe d58 v0 v2 v3 v3 v4 v5 v7
                (\ v9 -> coe d46 v0 v3 v5 (coe v8 v9))))
name158 = "Category.Monad.Indexed.RawIMonad._._<$_"
d158 v0 v1 v2 v3 v4 = du158 v4
du158 v0
  = coe MAlonzo.Code.Category.Applicative.Indexed.d86 erased erased
      erased
      erased
      (coe du146 v0)
name160 = "Category.Monad.Indexed.RawIMonad._._<$>_"
d160 v0 v1 v2 v3 v4 = du160 v4
du160 v0
  = coe MAlonzo.Code.Category.Applicative.Indexed.d88 erased erased
      erased
      erased
      (coe du146 v0)
name162 = "Category.Monad.Indexed.RawIMonad._._<\8859_"
d162 v0 v1 v2 v3 v4 = du162 v4
du162 v0
  = coe MAlonzo.Code.Category.Applicative.Indexed.d100 erased erased
      erased
      erased
      (coe du146 v0)
name164 = "Category.Monad.Indexed.RawIMonad._._\8855_"
d164 v0 v1 v2 v3 v4 = du164 v4
du164 v0
  = coe MAlonzo.Code.Category.Applicative.Indexed.d132 erased erased
      erased
      erased
      (coe du146 v0)
name166 = "Category.Monad.Indexed.RawIMonad._._\8859_"
d166 v0 v1 v2 v3 v4 = du166 v4
du166 v0
  = coe MAlonzo.Code.Category.Applicative.Indexed.d68 (coe du146 v0)
name168 = "Category.Monad.Indexed.RawIMonad._._\8859>_"
d168 v0 v1 v2 v3 v4 = du168 v4
du168 v0
  = coe MAlonzo.Code.Category.Applicative.Indexed.d116 erased erased
      erased
      erased
      (coe du146 v0)
name170 = "Category.Monad.Indexed.RawIMonad._.pure"
d170 v0 v1 v2 v3 v4 = du170 v4
du170 v0
  = coe MAlonzo.Code.Category.Applicative.Indexed.d56 (coe du146 v0)
name172 = "Category.Monad.Indexed.RawIMonad._.rawFunctor"
d172 v0 v1 v2 v3 v4 = du172 v4
du172 v0
  = coe MAlonzo.Code.Category.Applicative.Indexed.d74 erased erased
      erased
      erased
      (coe du146 v0)
name174 = "Category.Monad.Indexed.RawIMonad._.zipWith"
d174 v0 v1 v2 v3 v4 = du174 v4
du174 v0
  = coe MAlonzo.Code.Category.Applicative.Indexed.d150 erased erased
      erased
      erased
      (coe du146 v0)
name184 = "Category.Monad.Indexed.RawIMonadZero"
d184 a0 a1 a2 a3 = ()

data T184 a0 a1 = C183 a0 a1
name204 = "Category.Monad.Indexed.RawIMonadZero.monad"
d204 v0
  = case coe v0 of
        C183 v1 v2 -> coe v1
        _ -> coe MAlonzo.RTE.mazUnreachableError
name212 = "Category.Monad.Indexed.RawIMonadZero.\8709"
d212 v0
  = case coe v0 of
        C183 v1 v2 -> coe v2
        _ -> coe MAlonzo.RTE.mazUnreachableError
name216 = "Category.Monad.Indexed.RawIMonadZero._._<$_"
d216 v0 v1 v2 v3 v4 = du216 v4
du216 v0 = coe du158 (coe d204 v0)
name218 = "Category.Monad.Indexed.RawIMonadZero._._<$>_"
d218 v0 v1 v2 v3 v4 = du218 v4
du218 v0 = coe du160 (coe d204 v0)
name220 = "Category.Monad.Indexed.RawIMonadZero._._<=<_"
d220 v0 v1 v2 v3 v4 = du220 v4
du220 v0 = coe d128 erased erased erased erased (coe d204 v0)
name222 = "Category.Monad.Indexed.RawIMonadZero._._<\8859_"
d222 v0 v1 v2 v3 v4 = du222 v4
du222 v0 = coe du162 (coe d204 v0)
name224 = "Category.Monad.Indexed.RawIMonadZero._._=<<_"
d224 v0 v1 v2 v3 v4 v5 v6 v7
  = coe d58 (coe d204 v0) v1 v2 v3 v4 v5 v7 v6
name226 = "Category.Monad.Indexed.RawIMonadZero._._>=>_"
d226 v0 v1 v2 v3 v4 = du226 v4
du226 v0 = coe d108 erased erased erased erased (coe d204 v0)
name228 = "Category.Monad.Indexed.RawIMonadZero._._>>_"
d228 v0 v1 v2 v3 v4 v5 v6 v7
  = coe d58 (coe d204 v0) v1 v2 v3 v4 v5 v6 (\ v8 -> v7)
name230 = "Category.Monad.Indexed.RawIMonadZero._._>>=_"
d230 v0 = coe d58 (coe d204 v0)
name232 = "Category.Monad.Indexed.RawIMonadZero._._\8855_"
d232 v0 v1 v2 v3 v4 = du232 v4
du232 v0 = coe du164 (coe d204 v0)
name234 = "Category.Monad.Indexed.RawIMonadZero._._\8859_"
d234 v0 v1 v2 v3 v4 = du234 v4
du234 v0 = coe du166 (coe d204 v0)
name236 = "Category.Monad.Indexed.RawIMonadZero._._\8859>_"
d236 v0 v1 v2 v3 v4 = du236 v4
du236 v0 = coe du168 (coe d204 v0)
name238 = "Category.Monad.Indexed.RawIMonadZero._.join"
d238 v0 v1 v2 v3 v4 = du238 v3 v4
du238 v0 v1 = coe d142 erased erased erased v0 (coe d204 v1)
name240 = "Category.Monad.Indexed.RawIMonadZero._.pure"
d240 v0 v1 v2 v3 v4 = du240 v4
du240 v0 = coe du170 (coe d204 v0)
name242 = "Category.Monad.Indexed.RawIMonadZero._.rawFunctor"
d242 v0 v1 v2 v3 v4 = du242 v4
du242 v0 = coe du172 (coe d204 v0)
name244 = "Category.Monad.Indexed.RawIMonadZero._.rawIApplicative"
d244 v0 v1 v2 v3 v4 = du244 v4
du244 v0 = coe du146 (coe d204 v0)
name246 = "Category.Monad.Indexed.RawIMonadZero._.return"
d246 v0 = coe d46 (coe d204 v0)
name248 = "Category.Monad.Indexed.RawIMonadZero._.zipWith"
d248 v0 v1 v2 v3 v4 = du248 v4
du248 v0 = coe du174 (coe d204 v0)
name258 = "Category.Monad.Indexed.RawIMonadPlus"
d258 a0 a1 a2 a3 = ()

data T258 a0 a1 = C197 a0 a1
name278 = "Category.Monad.Indexed.RawIMonadPlus.monadZero"
d278 v0
  = case coe v0 of
        C197 v1 v2 -> coe v1
        _ -> coe MAlonzo.RTE.mazUnreachableError
name286 = "Category.Monad.Indexed.RawIMonadPlus._\8739_"
d286 v0
  = case coe v0 of
        C197 v1 v2 -> coe v2
        _ -> coe MAlonzo.RTE.mazUnreachableError
name290 = "Category.Monad.Indexed.RawIMonadPlus._._<$_"
d290 v0 v1 v2 v3 v4 = du290 v4
du290 v0 = coe du216 (coe d278 v0)
name292 = "Category.Monad.Indexed.RawIMonadPlus._._<$>_"
d292 v0 v1 v2 v3 v4 = du292 v4
du292 v0 = coe du218 (coe d278 v0)
name294 = "Category.Monad.Indexed.RawIMonadPlus._._<=<_"
d294 v0 v1 v2 v3 v4 = du294 v4
du294 v0 = coe du220 (coe d278 v0)
name296 = "Category.Monad.Indexed.RawIMonadPlus._._<\8859_"
d296 v0 v1 v2 v3 v4 = du296 v4
du296 v0 = coe du222 (coe d278 v0)
name298 = "Category.Monad.Indexed.RawIMonadPlus._._=<<_"
d298 v0 v1 v2 v3 v4 v5 v6 v7
  = coe d58 (coe d204 (coe d278 v0)) v1 v2 v3 v4 v5 v7 v6
name300 = "Category.Monad.Indexed.RawIMonadPlus._._>=>_"
d300 v0 v1 v2 v3 v4 = du300 v4
du300 v0 = coe du226 (coe d278 v0)
name302 = "Category.Monad.Indexed.RawIMonadPlus._._>>_"
d302 v0 v1 v2 v3 v4 v5 v6 v7
  = coe d58 (coe d204 (coe d278 v0)) v1 v2 v3 v4 v5 v6 (\ v8 -> v7)
name304 = "Category.Monad.Indexed.RawIMonadPlus._._>>=_"
d304 v0 = coe d58 (coe d204 (coe d278 v0))
name306 = "Category.Monad.Indexed.RawIMonadPlus._._\8855_"
d306 v0 v1 v2 v3 v4 = du306 v4
du306 v0 = coe du232 (coe d278 v0)
name308 = "Category.Monad.Indexed.RawIMonadPlus._._\8859_"
d308 v0 v1 v2 v3 v4 = du308 v4
du308 v0 = coe du234 (coe d278 v0)
name310 = "Category.Monad.Indexed.RawIMonadPlus._._\8859>_"
d310 v0 v1 v2 v3 v4 = du310 v4
du310 v0 = coe du236 (coe d278 v0)
name312 = "Category.Monad.Indexed.RawIMonadPlus._.join"
d312 v0 v1 v2 v3 v4 = du312 v3 v4
du312 v0 v1 = coe du238 v0 (coe d278 v1)
name314 = "Category.Monad.Indexed.RawIMonadPlus._.monad"
d314 v0 = coe d204 (coe d278 v0)
name316 = "Category.Monad.Indexed.RawIMonadPlus._.pure"
d316 v0 v1 v2 v3 v4 = du316 v4
du316 v0 = coe du240 (coe d278 v0)
name318 = "Category.Monad.Indexed.RawIMonadPlus._.rawFunctor"
d318 v0 v1 v2 v3 v4 = du318 v4
du318 v0 = coe du242 (coe d278 v0)
name320 = "Category.Monad.Indexed.RawIMonadPlus._.rawIApplicative"
d320 v0 v1 v2 v3 v4 = du320 v4
du320 v0 = coe du244 (coe d278 v0)
name322 = "Category.Monad.Indexed.RawIMonadPlus._.return"
d322 v0 = coe d46 (coe d204 (coe d278 v0))
name324 = "Category.Monad.Indexed.RawIMonadPlus._.zipWith"
d324 v0 v1 v2 v3 v4 = du324 v4
du324 v0 = coe du248 (coe d278 v0)
name326 = "Category.Monad.Indexed.RawIMonadPlus._.\8709"
d326 v0 = coe d212 (coe d278 v0)