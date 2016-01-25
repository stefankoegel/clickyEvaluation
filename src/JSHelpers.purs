module JSHelpers where

import Control.Monad.Eff
import Control.Monad.Eff.JQuery
import Data.Foreign
import DOM
import Prelude hiding (append)

foreign import jqMap :: forall eff. (JQuery -> Eff (dom :: DOM | eff) Unit) -> JQuery -> Eff (dom :: DOM | eff) Unit

foreign import isEnterKey :: JQueryEvent -> Boolean

foreign import createCanvas :: forall eff. Eff (dom :: DOM | eff) Foreign


 -- extension of  JQuery interface
foreign import offsetTop :: forall eff. JQuery -> Eff (dom :: DOM | eff) Number

foreign import offsetLeft :: forall eff. JQuery -> Eff (dom :: DOM | eff) Number

foreign import outerHeight :: forall eff. JQuery -> Eff (dom :: DOM | eff) Number

foreign import outerWidth :: forall eff. JQuery -> Eff (dom :: DOM | eff) Number

-- interface to Raphael libary
-- Foreign is Canvas from createCanvas
-- 2nd is SVG path
foreign import path:: forall eff. Foreign -> String -> Eff (dom :: DOM | eff ) Unit
