module JSHelpers where

import Control.Monad.Eff
import Control.Monad.Eff.JQuery
import Data.Foreign
import DOM
import Prelude hiding (append)

foreign import jqMap :: forall eff. (JQuery -> Eff (dom :: DOM | eff) Unit) -> JQuery -> Eff (dom :: DOM | eff) Unit

foreign import isEnterKey :: JQueryEvent -> Boolean

foreign import createCanvas :: forall eff. Eff (dom :: DOM | eff) Foreign
