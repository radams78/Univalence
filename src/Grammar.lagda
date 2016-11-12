\input{Grammar/Taxonomy}
\AgdaHide{
\begin{code}
open import Grammar.Taxonomy public
\end{code}
}

\input{Grammar/Base}
\AgdaHide{
\begin{code}
open import Grammar.Base public

module Grammar (G : Grammar) where
open Grammar G public
\end{code}
}

\input{Grammar/OpFamily}
\AgdaHide{
\begin{code}
open import Grammar.OpFamily G public
\end{code}
}

\input{Grammar/Replacement}
\AgdaHide{
\begin{code}
open import Grammar.Replacement G public
\end{code}
}

\input{Grammar/Replacement/SetFunctor}
\AgdaHide{
\begin{code}
open import Grammar.Replacement.SetFunctor G public
\end{code}
}

\input{Grammar/Substitution}
\AgdaHide{
\begin{code}
open import Grammar.Substitution G public
\end{code}
}

\input{Grammar/Context}
\AgdaHide{
\begin{code}
open import Grammar.Context G public
\end{code}
}
