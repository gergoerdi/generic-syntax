\begin{code}[hide]
module GenericSyntax.Util where
\end{code}

%<*Mapping>
\begin{code}
_→̇_ : ∀ {a b c} {A : Set a} → (A → Set b) → (A → Set c) → Set _
F →̇ G = ∀ {t} → F t → G t
\end{code}
%</Mapping>

\begin{code}
_→̈_ : ∀ {a b c d} {A : Set a} {B : Set b} → (A → B → Set c) → (A → B → Set d) → Set _
F →̈ G = ∀ {Γ t} → F Γ t → G Γ t
\end{code}
