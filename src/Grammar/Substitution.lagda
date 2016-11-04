\AgdaHide{
\begin{code}
open import Grammar.Base

module Grammar.Substitution (G : Grammar) where
\end{code}
}

\input{Grammar/Substitution/PreOpFamily}
\AgdaHide{
\begin{code}
open import Grammar.Substitution.PreOpFamily G public
\end{code}
}

\input{Grammar/Substitution/Lifting}
\AgdaHide{
\begin{code}
open import Grammar.Substitution.Lifting G public
\end{code}
}

\input{Grammar/Substitution/RepSub}
\AgdaHide{
\begin{code}
open import Grammar.Substitution.RepSub G public
\end{code}
}

\input{Grammar/Substitution/LiftFamily}
\AgdaHide{
\begin{code}
open import Grammar.Substitution.LiftFamily G public
\end{code}
}

\input{Grammar/Substitution/OpFamily}
\AgdaHide{
\begin{code}
open import Grammar.Substitution.OpFamily G public
\end{code}
}

\input{Grammar/Substitution/Botsub}
\AgdaHide{
\begin{code}
open import Grammar.Substitution.Botsub G public
\end{code}
}
