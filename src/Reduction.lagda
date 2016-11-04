\AgdaHide{
\begin{code}
open import Grammar.Base

module Reduction (G : Grammar) (R : Grammar.Reduction G) where
\end{code}
}

\input{Reduction/Base}
\AgdaHide{
\begin{code}
open import Reduction.Base G R public
\end{code}
}

\input{Reduction/SN}
\AgdaHide{
\begin{code}
open import Reduction.SN G R public
\end{code}
}

\input{Reduction/Botsub}
\AgdaHide{
\begin{code}
open import Reduction.Botsub G R public
\end{code}
}
