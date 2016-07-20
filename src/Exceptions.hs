module Exceptions where

data Exceptional e a =
     Success a
   | Exception e
   deriving (Show)

instance Applicative (Exceptional e)
instance Functor (Exceptional e)

instance Monad (Exceptional e) where
   return              =  Success
   Exception l >>= _   =  Exception l
   Success  r  >>= k   =  k r

throw :: e -> Exceptional e a
throw = Exception

catch :: Exceptional e a -> (e -> Exceptional e a) -> Exceptional e a
catch (Exception  l) h = h l
catch (Success r)    _ = Success r

newtype ExceptionalT e m a =
   ExceptionalT {runExceptionalT :: m (Exceptional e a)}

instance Monad m => Monad (ExceptionalT e m) where
   return   =  ExceptionalT . return . Success
   m >>= k  =  ExceptionalT $
      runExceptionalT m >>= \ a ->
         case a of
            Exception e -> return (Exception e)
            Success   r -> runExceptionalT (k r)

throwT :: Monad m => e -> ExceptionalT e m a
throwT = ExceptionalT . return . Exception

catchT :: Monad m =>
   ExceptionalT e m a -> (e -> ExceptionalT e m a) -> ExceptionalT e m a
catchT m h = ExceptionalT $
   runExceptionalT m >>= \ a ->
      case a of
         Exception l -> runExceptionalT (h l)
         Success   r -> return (Success r)

bracketT :: Monad m =>
   ExceptionalT e m h ->
   (h -> ExceptionalT e m ()) ->
   (h -> ExceptionalT e m a) ->
   ExceptionalT e m a
bracketT open close body =
   open >>= (\ h ->
      ExceptionalT $
         do a <- runExceptionalT (body h)
            runExceptionalT (close h)
            return a)
