module JSHelpers (jqMap, isEnterKey, showTooltip, children, prepend, warnOnRefresh, ctrlKeyPressed,showTypes) where

import Control.Monad.Eff (Eff)
import Control.Monad.Eff.JQuery (JQuery, JQueryEvent,Selector)
import DOM (DOM)
import Prelude (Unit)

foreign import jqMap :: forall eff. (JQuery -> Eff (dom :: DOM | eff) Unit) -> JQuery -> Eff (dom :: DOM | eff) Unit

foreign import isEnterKey :: JQueryEvent -> Boolean

foreign import ctrlKeyPressed :: JQueryEvent -> Boolean

foreign import showTooltip ::forall eff. JQuery -> JQuery -> JQueryEvent -> Eff (dom :: DOM | eff) Unit

foreign import children :: forall eff. Selector -> JQuery -> Eff (dom :: DOM | eff) JQuery

foreign import prepend :: forall eff. JQuery -> JQuery -> Eff (dom :: DOM | eff) JQuery

foreign import warnOnRefresh :: forall eff. Eff (dom :: DOM | eff) Unit

foreign import showTypes :: forall eff. Eff (dom:: DOM | eff) Unit
