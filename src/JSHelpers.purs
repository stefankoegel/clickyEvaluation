module JSHelpers (jqMap, isEnterKey, showTooltip) where

import Control.Monad.Eff (Eff)
import Control.Monad.Eff.JQuery (JQuery, JQueryEvent)
import DOM (DOM)
import Prelude (Unit)
import Data.Foreign

foreign import jqMap :: forall eff. (JQuery -> Eff (dom :: DOM | eff) Unit) -> JQuery -> Eff (dom :: DOM | eff) Unit

foreign import isEnterKey :: JQueryEvent -> Boolean

foreign import showTooltip ::forall eff. JQuery -> JQuery -> JQueryEvent -> Eff (dom :: DOM | eff) Unit
