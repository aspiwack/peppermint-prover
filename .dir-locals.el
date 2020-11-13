;;; Directory Local Variables
;;; For more information see (info "(emacs) Directory Variables")

((nil . ((eval . (add-hook 'hack-local-variables-hook
                           (lambda nil
                             (when
                                 (derived-mode-p 'haskell-mode)
                               (lsp))))))))
