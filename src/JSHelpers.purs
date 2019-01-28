module JSHelpers where

import Effect (Effect)
import JQuery (JQuery, JQueryEvent, Selector)
import Prelude (Unit)

foreign import jqMap :: (JQuery -> Effect Unit) -> JQuery -> Effect Unit

foreign import isEnterKey :: JQueryEvent -> Boolean

foreign import ctrlKeyPressed :: JQueryEvent -> Boolean

foreign import getType :: JQueryEvent -> String

foreign import showTooltip :: JQuery -> JQuery -> JQueryEvent -> Effect Unit

foreign import children :: Selector -> JQuery -> Effect JQuery

foreign import prepend :: JQuery -> JQuery -> Effect JQuery

foreign import warnOnRefresh :: Effect Unit

foreign import showTypes :: Effect Unit

foreign import isChecked :: JQuery -> Effect Boolean

foreign import unsafeUndef :: forall a. String -> a
