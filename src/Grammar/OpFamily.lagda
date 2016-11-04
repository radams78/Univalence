\AgdaHide{
\begin{code}
open import Grammar.Base

module Grammar.OpFamily (G : Grammar) where
\end{code}
}

\input{Grammar/OpFamily/PreOpFamily}
\AgdaHide{
\begin{code}
open import Grammar.OpFamily.PreOpFamily G public
\end{code}
}

\input{Grammar/OpFamily/Lifting}
\AgdaHide{
\begin{code}
open import Grammar.OpFamily.Lifting G public
\end{code}
}

\input{Grammar/OpFamily/LiftFamily}
\AgdaHide{
\begin{code}
open import Grammar.OpFamily.LiftFamily G public
\end{code}
}

\input{Grammar/OpFamily/Composition}
\AgdaHide{
\begin{code}
open import Grammar.OpFamily.Composition G public
\end{code}
}

\input{Grammar/OpFamily/OpFamily}
\AgdaHide{
\begin{code}
open import Grammar.OpFamily.OpFamily G public
\end{code}
}