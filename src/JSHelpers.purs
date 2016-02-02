module JSHelpers (jqMap, isEnterKey) where

import Control.Monad.Eff (Eff)
import Control.Monad.Eff.JQuery (JQuery, JQueryEvent)
import DOM (DOM)
import Prelude (Unit)

foreign import jqMap :: forall eff. (JQuery -> Eff (dom :: DOM | eff) Unit) -> JQuery -> Eff (dom :: DOM | eff) Unit

foreign import isEnterKey :: JQueryEvent -> Boolean
