import React, { useState, useRef, useEffect, useCallback, useMemo } from 'react';
// 新增引入 Image as ImageIcon 以避免名稱衝突
import { Upload, Move, RefreshCw, ChevronUp, ChevronDown, ChevronLeft, ChevronRight, Ruler, ArrowLeft, ArrowRight, Loader2, Minus, Plus, Maximize2, Minimize2, MousePointerClick, Download, Save, FileJson, FileImage, Image as ImageIcon, Wand2 } from 'lucide-react';

// 改為最小目標寬度，不再是固定寬度
const MIN_TARGET_WIDTH = 1000; 
// 為了瀏覽器效能，設定一個合理的上限 (4K解析度寬度)
const MAX_TARGET_WIDTH = 4096;
// 顯示用的基礎寬度限制
const BASE_TARGET_WIDTH = 1000;

const MAGNIFIER_SIZE = 225; 

// --- 輔助函數: 圖片載入 ---
const loadImage = (src) => {
    return new Promise((resolve, reject) => {
        const img = new Image();
        img.crossOrigin = "anonymous"; 
        img.onload = () => resolve(img);
        img.onerror = (e) => reject(new Error("圖片載入失敗，請確認檔案格式是否正確。"));
        img.src = src;
    });
};

// --- 核心函數: 矩陣運算工具 (Matrix Utility) ---
const Matrix = {
    // 矩陣乘法 (A * B)
    multiply: (A, B) => {
        const rowsA = A.length, colsA = A[0].length;
        const rowsB = B.length, colsB = B[0].length;

        if (colsA !== rowsB) throw new Error("矩陣尺寸不匹配");
        
        const C = Array(rowsA).fill(0).map(() => Array(colsB).fill(0));
        
        for (let i = 0; i < rowsA; i++) {
            for (let j = 0; j < colsB; j++) {
                let sum = 0;
                for (let k = 0; k < colsA; k++) {
                    sum += A[i][k] * B[k][j];
                }
                C[i][j] = sum;
            }
        }
        return C;
    },

    // 矩陣求逆
    inverse3x3: (M) => {
        const [a, b, c, d, e, f, g, h, i] = [
            M[0][0], M[0][1], M[0][2],
            M[1][0], M[1][1], M[1][2],
            M[2][0], M[2][1], M[2][2]
        ];

        const det = a * (e * i - f * h) - b * (d * i - f * g) + c * (d * h - e * g);
        if (Math.abs(det) < 1e-6) return null;
        const invDet = 1 / det;

        return [
            [(e * i - f * h) * invDet, (c * h - b * i) * invDet, (b * f - c * e) * invDet],
            [(f * g - d * i) * invDet, (a * i - c * g) * invDet, (c * d - a * f) * invDet],
            [(d * h - e * g - 0) * invDet, (b * g - a * h) * invDet, (a * e - b * d) * invDet]
        ];
    },
    
    // 求解 Ax=B 的線性系統
    solveLinearSystem: (A, B) => {
        const n = A.length;
        const M = A.map((row, i) => [...row, B[i]]);

        for (let k = 0; k < n; k++) {
            let i_max = k;
            let v_max = M[k][k];
            for (let i = k + 1; i < n; i++) {
                if (Math.abs(M[i][k]) > Math.abs(v_max)) {
                    v_max = M[i][k];
                    i_max = i;
                }
            }
            if (M[i_max][k] === 0) throw new Error("線性系統奇異");
            
            [M[k], M[i_max]] = [M[i_max], M[k]];

            for (let i = k + 1; i < n; i++) {
                const f = M[i][k] / M[k][k];
                for (let j = k; j < n + 1; j++) {
                    M[i][j] = M[i][j] - M[k][j] * f;
                }
            }
        }

        const X = Array(n).fill(0); 
        for (let i = n - 1; i >= 0; i--) {
            let sum = 0;
            for (let j = i + 1; j < n; j++) sum += M[i][j] * X[j];
            X[i] = (M[i][n] - sum) / M[i][i]; 
        }
        return X;
    }
};

// --- 核心函數: 雙線性插值 ---
const bilinearInterpolation = (imageData, x, y) => {
    const { width, height, data } = imageData;
    const x1 = Math.floor(x), y1 = Math.floor(y);
    const x2 = Math.ceil(x), y2 = Math.ceil(y);

    if (x1 < 0 || x2 >= width || y1 < 0 || y2 >= height) return [0, 0, 0, 255]; 

    const fx = x - x1, fy = y - y1;
    const fx1 = 1 - fx, fy1 = 1 - fy;

    const getPixelIndex = (px, py) => (py * width + px) * 4;
    let r = 0, g = 0, b = 0, a = 0;
    
    // Helper for interpolation
    const interpolate = (idx, w) => {
        r += data[idx] * w; g += data[idx + 1] * w; b += data[idx + 2] * w; a += data[idx + 3] * w;
    }
    
    interpolate(getPixelIndex(x1, y1), fx1 * fy1);
    interpolate(getPixelIndex(x2, y1), fx * fy1);
    interpolate(getPixelIndex(x1, y2), fx1 * fy);
    interpolate(getPixelIndex(x2, y2), fx * fy);

    return [Math.round(r), Math.round(g), Math.round(b), Math.round(a)];
};

// --- 放大鏡組件 (Magnifier Component) ---
const Magnifier = React.memo(({ magnifierState, zoom, cardImage }) => { 
    const { visible, targetX, targetY, imgRect, currentStep, cropPoints, measureLines } = magnifierState;
    const canvasRef = useRef(null);
    
    // 動態計算放大鏡尺寸
    const size = useMemo(() => {
        if (zoom >= 3) return MAGNIFIER_SIZE * 2;   // 3倍或以上 -> 2倍半徑 (範圍更大)
        if (zoom >= 2) return MAGNIFIER_SIZE * 1.5; // 2倍 -> 1.5倍半徑
        return MAGNIFIER_SIZE;                      // 其他 -> 原始大小
    }, [zoom]);

    const halfSize = size / 2;

    useEffect(() => {
        if (!visible || !canvasRef.current || !cardImage || !imgRect || imgRect.width === 0) return;

        const canvas = canvasRef.current;
        const ctx = canvas.getContext('2d');
        
        canvas.width = size;
        canvas.height = size;
        
        const img = cardImage;
        if (!img.complete) return; 

        // 1. 繪製放大後的圖像
        const normX = (targetX - imgRect.left);
        const normY = (targetY - imgRect.top);
        
        const imgW = img.naturalWidth;
        const imgH = img.naturalHeight;
        
        const imgRenderW = imgRect.width;
        const imgRenderH = imgRect.height;
        
        const norm_x_01 = normX / imgRenderW;
        const norm_y_01 = normY / imgRenderH;
        
        const srcX = norm_x_01 * imgW;
        const srcY = norm_y_01 * imgH;
        
        const clipW_px = size / zoom; 
        const clipH_px = size / zoom; 
        
        ctx.clearRect(0, 0, size, size);
        try {
            // 繪製裁切區域
            ctx.drawImage(img, srcX - clipW_px / 2, srcY - clipH_px / 2, clipW_px, clipH_px, 0, 0, size, size);
        } catch (e) {
            console.error("Magnifier drawImage failed:", e);
        }
        
        // 2. 繪製線條與點位
        const scale = size / clipW_px; 
        const offsetX = (srcX * scale) - halfSize;
        const offsetY = (srcY * scale) - halfSize;
        
        ctx.lineWidth = 2;
        // 設置虛線樣式 (用於測量和裁切線)
        ctx.setLineDash([5, 5]); 

        const drawNormalizedPoint = (norm_x, norm_y) => ({
            x: (norm_x * imgW * scale) - offsetX,
            y: (norm_y * imgH * scale) - offsetY,
        });

        if (currentStep === 'crop' && cropPoints && cropPoints.length === 4) {
            // 裁切框 (綠色虛線)
            ctx.strokeStyle = 'rgba(34, 197, 94, 1)'; 
            ctx.beginPath();
            const startPt = drawNormalizedPoint(cropPoints[0].x, cropPoints[0].y);
            ctx.moveTo(startPt.x, startPt.y);
            cropPoints.forEach((p, i) => {
                const pt = drawNormalizedPoint(p.x, p.y);
                if (i > 0) ctx.lineTo(pt.x, pt.y);
            });
            ctx.lineTo(startPt.x, startPt.y);
            ctx.stroke();

            // 裁切點 (綠色實心圓)
            ctx.setLineDash([]); // 圓形不需要虛線
            cropPoints.forEach((p) => {
                const pt = drawNormalizedPoint(p.x, p.y);
                ctx.fillStyle = 'rgba(34, 197, 94, 1)'; 
                ctx.beginPath();
                ctx.arc(pt.x, pt.y, 4 / Math.sqrt(zoom), 0, Math.PI * 2); 
                ctx.fill();
            });
            ctx.setLineDash([5, 5]); // 恢復虛線模式
        } else if (currentStep === 'measure' && measureLines) {
            // 測量線 (藍色/紅色虛線)
            const lines = measureLines;
            const drawLine = (val, isH, color) => {
                ctx.strokeStyle = color;
                ctx.beginPath();
                if (isH) {
                    const y = ((val / 100) * imgH * scale) - offsetY;
                    ctx.moveTo(0, y); ctx.lineTo(size, y);
                } else {
                    const x = ((val / 100) * imgW * scale) - offsetX;
                    ctx.moveTo(x, 0); ctx.lineTo(x, size);
                }
                ctx.stroke();
            };

            // 藍線 (卡邊)
            drawLine(lines.outerTop, true, 'rgba(59, 130, 246, 1)');
            drawLine(lines.outerBottom, true, 'rgba(59, 130, 246, 1)');
            drawLine(lines.outerLeft, false, 'rgba(59, 130, 246, 1)');
            drawLine(lines.outerRight, false, 'rgba(59, 130, 246, 1)');
            
            // 紅線 (圖案邊界)
            drawLine(lines.innerTop, true, 'rgba(239, 68, 68, 1)');
            drawLine(lines.innerBottom, true, 'rgba(239, 68, 68, 1)');
            drawLine(lines.innerLeft, false, 'rgba(239, 68, 68, 1)');
            drawLine(lines.innerRight, false, 'rgba(239, 68, 68, 1)');
        }
        
        // 3. 繪製中心紅點 (實心圓)
        ctx.setLineDash([]); 
        ctx.fillStyle = 'rgba(255, 0, 0, 0.8)';
        ctx.beginPath();
        ctx.arc(halfSize, halfSize, 3, 0, Math.PI * 2);
        ctx.fill();

    }, [visible, targetX, targetY, imgRect, cardImage, size, zoom, currentStep, cropPoints, measureLines]);

    if (!visible || !imgRect || imgRect.width === 0) return null;

    const finalLeft = targetX - halfSize;
    const finalTop = targetY - halfSize;

    const style = {
        left: `${finalLeft}px`, top: `${finalTop}px`, width: `${size}px`, height: `${size}px`,
    };

    return (
        // 放大鏡使用 fixed 定位是正確的，因為它跟隨滑鼠/觸控位置
        <div className="fixed rounded-full shadow-2xl z-[100] border-4 border-yellow-400 backdrop-blur-sm transition-opacity duration-150 overflow-hidden bg-gray-900/50" style={style}>
            <canvas ref={canvasRef} className="rounded-full w-full h-full"></canvas>
        </div>
    );
});


function CardGraderTool() {
  const [step, setStep] = useState('upload'); 
  const [originalImage, setOriginalImage] = useState(null); 
  // 記錄原始檔名，方便下載 JSON 時命名
  const [originalFileName, setOriginalFileName] = useState("card"); 
  const [processedImage, setProcessedImage] = useState(null); 
  const [isProcessing, setIsProcessing] = useState(false);
  const [zoomLevel, setZoomLevel] = useState(1.0); 
  // 新增: 用於顯示 HEIC 轉換中的狀態文字
  const [loadingText, setLoadingText] = useState("正在進行透視校正 (Homography)...");
  
  // 新增: 暫存載入的 JSON 設定檔
  const [pendingProjectData, setPendingProjectData] = useState(null);

  // 新增: 控制放大鏡面板收折狀態
  const [isMagnifierPanelCollapsed, setIsMagnifierPanelCollapsed] = useState(false);

  const [originalCardDims, setOriginalCardDims] = useState({ w: 0, h: 0 }); 
  const [cropPoints, setCropPoints] = useState([]); 
  const [activePointIndex, setActivePointIndex] = useState(null);
  
  // 新增: 記錄最後操作的綠點 (0:左上, 1:右上, 2:右下, 3:左下)
  const [lastActivePointIndex, setLastActivePointIndex] = useState(null);

  // 新增: 記錄是否正在進行一般拖曳（空白處檢查）
  const [isGeneralDragging, setIsGeneralDragging] = useState(false);

  const [measureLines, setMeasureLines] = useState({
    outerTop: 2, innerTop: 12, outerBottom: 98, innerBottom: 88,
    outerLeft: 3, innerLeft: 13, outerRight: 97, innerRight: 87
  });
  
  const measureLinesRef = useRef(measureLines);
  useEffect(() => { measureLinesRef.current = measureLines; }, [measureLines]);

  const [selectedLineId, setSelectedLineId] = useState(null); 
  const [draggingLineId, setDraggingLineId] = useState(null); 
  const [lastInteractionCoords, setLastInteractionCoords] = useState({});
  const currentMousePosRef = useRef({ clientX: 0, clientY: 0 });

  const [magnifier, setMagnifier] = useState({ 
      visible: false, targetX: 0, targetY: 0, imgRect: null, 
      currentStep: 'upload', cropPoints: [], measureLines: {}, isTrackingMouse: false
  }); 

  const containerRef = useRef(null);
  const imgRef = useRef(null);
  const magnifierTimeoutRef = useRef(null); 

  const cardImageForMagnifier = useMemo(() => {
    if (step === 'crop' && originalImage) return originalImage; 
    if (step === 'measure' && processedImage) return processedImage;
    return null;
  }, [step, originalImage, processedImage]);

  const zoomOptions = [0.2, 0.5, 1.0, 1.5, 2, 3, 5];

  // --- Helper: Get Live Image Rect (Crucial for scrolling/coordinate stability) ---
  const getLiveImageRect = useCallback(() => {
    if (!imgRef.current) return null;
    return imgRef.current.getBoundingClientRect();
  }, []);

  // --- Helper: Get Live Container Rect ---
  const getLiveContainerRect = useCallback(() => {
    if (!containerRef.current) return null;
    return containerRef.current.getBoundingClientRect();
  }, []);

  // --- Helper: Show Fixed Magnifier ---
  const showFixedMagnifierAt = useCallback((clientX, clientY) => {
    const imgRect = getLiveImageRect(); // 使用即時 Rect
    if (!imgRect || imgRect.width === 0) return;

    if (magnifierTimeoutRef.current) {
        clearTimeout(magnifierTimeoutRef.current);
        magnifierTimeoutRef.current = null;
    }
    
    setMagnifier(prev => ({
        ...prev, visible: true, isTrackingMouse: false, 
        targetX: clientX, targetY: clientY, imgRect: imgRect,
        currentStep: step, cropPoints: cropPoints, measureLines: measureLinesRef.current, 
    }));

    magnifierTimeoutRef.current = setTimeout(() => {
        setMagnifier(prev => ({ ...prev, visible: false, isTrackingMouse: false }));
        magnifierTimeoutRef.current = null;
    }, 2000); 
  }, [step, cropPoints, measureLinesRef, getLiveImageRect]); 

  // --- Helper: Get Screen Coordinates ---
  const getLineScreenCenter = useCallback((lineId) => {
    if (!lineId || !processedImage) return null;
    const imgRect = getLiveImageRect(); // 使用即時 Rect
    if (!imgRect || imgRect.width === 0) return null;

    const storedCoords = lastInteractionCoords[lineId];
    if (storedCoords) return storedCoords;

    const isH = lineId.includes('Top') || lineId.includes('Bottom');
    const lineVal = measureLinesRef.current[lineId] / 100; 

    let screenX, screenY;
    if (isH) {
        screenX = imgRect.left + imgRect.width / 2;
        screenY = imgRect.top + imgRect.height * lineVal;
    } else {
        screenX = imgRect.left + imgRect.width * lineVal;
        screenY = imgRect.top + imgRect.height / 2;
    }
    return { x: screenX, y: screenY };
  }, [processedImage, lastInteractionCoords, measureLinesRef, getLiveImageRect]);

  // --- Handlers: Soft Reset (跳回首頁，不刷新頁面) ---
  const handleReset = () => {
      setStep('upload');
      setOriginalImage(null);
      setProcessedImage(null);
      setPendingProjectData(null);
      setOriginalFileName("card");
      setZoomLevel(1.0);
      setLastActivePointIndex(null);
      setSelectedLineId(null);
      setDraggingLineId(null);
      setIsGeneralDragging(false); // Reset general dragging state
      // 重置測量線為預設值
      setMeasureLines({
        outerTop: 2, innerTop: 12, outerBottom: 98, innerBottom: 88,
        outerLeft: 3, innerLeft: 13, outerRight: 97, innerRight: 87
      });
      // 這裡不需要重置 cropPoints，因為下次上傳圖片時 handleImageUpload 會自動重置
  };

  // --- Handlers: JSON Import ---
  const handleJsonUpload = (e) => {
      const file = e.target.files[0];
      if (!file) return;

      const reader = new FileReader();
      reader.onload = (event) => {
          try {
              const data = JSON.parse(event.target.result);
              if (data && data.cropPoints && data.measureLines) {
                  setPendingProjectData(data);
                  // 不再彈出 alert，直接改變 UI 狀態
              } else {
                  alert("錯誤：無效的專案設定檔 (JSON)");
              }
          } catch (err) {
              console.error("JSON parse error", err);
              alert("錯誤：無法讀取 JSON 檔案");
          }
      };
      reader.readAsText(file);
      // 清空 input 讓同名檔案可再次觸發
      e.target.value = '';
  };

  // --- Handlers: Export Project (JSON) ---
  const handleExportJSON = () => {
      if (!originalImage) return;
      
      const data = {
          version: "1.0",
          timestamp: Date.now(),
          imageName: originalFileName,
          cropPoints: cropPoints,
          measureLines: measureLines,
          results: calculateResults()
      };
      
      const jsonStr = JSON.stringify(data, null, 2);
      const blob = new Blob([jsonStr], { type: "application/json" });
      const url = URL.createObjectURL(blob);
      
      const link = document.createElement('a');
      // 移除副檔名，加上 .json
      const baseName = originalFileName.replace(/\.[^/.]+$/, "");
      link.download = `${baseName}_grading.json`;
      link.href = url;
      link.click();
      URL.revokeObjectURL(url);
  };

  // --- Handlers: Upload Image ---
  const handleImageUpload = async (e) => {
    const file = e.target.files[0];
    if (!file) return;
    
    // HEIC/HEIF 支援邏輯
    const isHeic = file.type === "image/heic" || file.type === "image/heif" || file.name.toLowerCase().endsWith(".heic") || file.name.toLowerCase().endsWith(".heif");

    if (isHeic) {
        setLoadingText("正在將 HEIC 格式轉換為 JPG...");
        setIsProcessing(true);
        try {
            // 動態導入 heic2any，避免初始 bundle 過大或依賴問題
            const heic2any = (await import('https://cdn.skypack.dev/heic2any')).default;
            
            const convertedBlob = await heic2any({
                blob: file,
                toType: "image/jpeg",
                quality: 0.8
            });
            
            // 處理轉換後的 Blob (可能是陣列，如果是 Live Photo)
            const finalBlob = Array.isArray(convertedBlob) ? convertedBlob[0] : convertedBlob;
            
            // 將 Blob 轉為 File 物件以便後續處理
            const convertedFile = new File([finalBlob], file.name.replace(/\.(heic|heif)$/i, ".jpg"), {
                type: "image/jpeg",
                lastModified: new Date().getTime()
            });
            
            // 遞迴調用 (模擬上傳 JPEG)
            // 這裡我們直接用 FileReader 讀取轉換後的 blob 比較快，不用遞迴
            processImageFile(convertedFile);
            
        } catch (error) {
            console.error("HEIC conversion failed:", error);
            alert("HEIC 轉換失敗，請確認網路連線 (需載入轉換庫) 或嘗試上傳 JPG/PNG。");
            setIsProcessing(false);
        }
    } else {
        // 標準 JPG/PNG 處理
        processImageFile(file);
    }
    
    e.target.value = ''; // 允許重複上傳同檔名
  };

  // 抽離出圖片處理邏輯
  const processImageFile = (file) => {
      setOriginalFileName(file.name); 
      const reader = new FileReader();
      reader.onload = (event) => {
        const img = new Image();
        img.crossOrigin = "anonymous";
        img.onload = () => {
          setOriginalImage(img);
          const dims = { w: img.naturalWidth, h: img.naturalHeight };
          setOriginalCardDims(dims); 
          
          if (pendingProjectData) {
              setCropPoints(pendingProjectData.cropPoints);
              setMeasureLines(pendingProjectData.measureLines);
              setPendingProjectData(null); 
              setProcessedImage(null); 
              setStep('crop');
          } else {
              const initialCropPoints = [
                { x: 0.15, y: 0.15 }, { x: 0.85, y: 0.15 }, 
                { x: 0.85, y: 0.85 }, { x: 0.15, y: 0.85 }, 
              ];
              setCropPoints(initialCropPoints);
              setProcessedImage(null); 
              setStep('crop');
          }
          setLastActivePointIndex(null);
          setIsProcessing(false); // 關閉 loading
        };
        img.src = event.target.result;
      };
      reader.readAsDataURL(file);
  };

  // --- Helper: Coordinate Mapping ---
  const getScreenCoords = useCallback((normX, normY) => {
    const imgRect = getLiveImageRect(); // 使用即時 Rect
    if (!imgRect || imgRect.width === 0) return { x: -100, y: -100 };

    return {
      x: normX * imgRect.width + imgRect.left,
      y: normY * imgRect.height + imgRect.top,
      renderW: imgRect.width, renderH: imgRect.height, 
      offsetX: imgRect.left, offsetY: imgRect.top 
    };
  }, [getLiveImageRect]);

  const handleCropDragStart = (index, e) => {
    e.preventDefault(); e.stopPropagation(); 
    setActivePointIndex(index); 
    setLastActivePointIndex(index); // 記錄這個點為最後活動點
    setSelectedLineId(null); 
    if (magnifierTimeoutRef.current) { clearTimeout(magnifierTimeoutRef.current); magnifierTimeoutRef.current = null; }
  };

  const handleLineDragStart = (id, e) => {
    e.stopPropagation(); 
    setSelectedLineId(id); setDraggingLineId(id); setActivePointIndex(null); 

    const clientX = e.touches ? e.touches[0].clientX : e.clientX;
    const clientY = e.touches ? e.touches[0].clientY : e.clientY;
    
    showFixedMagnifierAt(clientX, clientY);
    setLastInteractionCoords(prev => ({ ...prev, [id]: { x: clientX, y: clientY } }));
  };

  // 新增: 處理空白處拖曳 (一般放大鏡檢查)
  const handleGeneralDragStart = (e) => {
      // 確保不是點擊到了其他控制元素 (雖然結構上 div 已經覆蓋，但多一層保險)
      setIsGeneralDragging(true);
      const clientX = e.touches ? e.touches[0].clientX : e.clientX;
      const clientY = e.touches ? e.touches[0].clientY : e.clientY;
      
      const imgRect = getLiveImageRect();
      if(imgRect) {
           if (magnifierTimeoutRef.current) { clearTimeout(magnifierTimeoutRef.current); magnifierTimeoutRef.current = null; }
           setMagnifier(prev => ({ 
              ...prev, visible: true, isTrackingMouse: true, 
              targetX: clientX, targetY: clientY, imgRect: imgRect,
              measureLines: measureLinesRef.current, currentStep: step,
          }));
      }
  };

  // Shared move handler
  const handleGlobalMove = useCallback((e) => {
    if (!containerRef.current) return;
    const clientX = e.touches ? e.touches[0].clientX : e.clientX;
    const clientY = e.touches ? e.touches[0].clientY : e.clientY;
    currentMousePosRef.current = { clientX, clientY };

    // *** 關鍵: 直接從 DOM 讀取圖片的即時位置 Rect ***
    const imgRect = getLiveImageRect(); 
    if (!imgRect || imgRect.width === 0) return; 

    const relativeX = clientX - imgRect.left;
    const relativeY = clientY - imgRect.top;

    let normX = Math.max(0, Math.min(1, relativeX / imgRect.width));
    let normY = Math.max(0, Math.min(1, relativeY / imgRect.height));

    if (step === 'crop' && activePointIndex !== null) {
      if (magnifierTimeoutRef.current) { clearTimeout(magnifierTimeoutRef.current); magnifierTimeoutRef.current = null; }
      const nextCropPoints = [...cropPoints];
      nextCropPoints[activePointIndex] = { x: normX, y: normY };
      setCropPoints(nextCropPoints);
      
       setMagnifier(prev => ({ 
            ...prev, visible: true, isTrackingMouse: true, 
            targetX: clientX, targetY: clientY, imgRect: imgRect,
            currentStep: step, cropPoints: nextCropPoints, 
        }));

    } else if (step === 'measure' && draggingLineId) { 
       if (magnifierTimeoutRef.current) { clearTimeout(magnifierTimeoutRef.current); magnifierTimeoutRef.current = null; }
       
       const valPct = (draggingLineId.includes('Left') || draggingLineId.includes('Right')) 
          ? normX * 100 : normY * 100;
       
       setMeasureLines(prev => ({ ...prev, [draggingLineId]: valPct }));
       
       setMagnifier(prev => ({ 
            ...prev, visible: true, isTrackingMouse: true, 
            targetX: clientX, targetY: clientY, imgRect: imgRect,
            measureLines: measureLinesRef.current, currentStep: step,
        }));
        setLastInteractionCoords(prev => ({ ...prev, [draggingLineId]: { x: clientX, y: clientY } }));
    } else if (step === 'measure' && isGeneralDragging) {
        // 新增: 處理一般拖曳時的放大鏡更新
        if (magnifierTimeoutRef.current) { clearTimeout(magnifierTimeoutRef.current); magnifierTimeoutRef.current = null; }
        
        setMagnifier(prev => ({ 
            ...prev, visible: true, isTrackingMouse: true, 
            targetX: clientX, targetY: clientY, imgRect: imgRect,
            measureLines: measureLinesRef.current, currentStep: step,
        }));
    }
  }, [step, activePointIndex, draggingLineId, isGeneralDragging, cropPoints, getLiveImageRect, showFixedMagnifierAt]); 

  const handleGlobalUp = useCallback(() => {
    const wasCropDragging = activePointIndex !== null;
    const wasLineDragging = draggingLineId !== null;
    const wasGeneralDragging = isGeneralDragging;
    
    setActivePointIndex(null); 
    setDraggingLineId(null); 
    setIsGeneralDragging(false);
    
    if (wasCropDragging || wasLineDragging || wasGeneralDragging) {
          setMagnifier(prev => ({ ...prev, visible: false, isTrackingMouse: false }));
          if (magnifierTimeoutRef.current) { clearTimeout(magnifierTimeoutRef.current); magnifierTimeoutRef.current = null; }
    }
  }, [draggingLineId, activePointIndex, isGeneralDragging]); 

  useEffect(() => {
    window.addEventListener('mousemove', handleGlobalMove);
    window.addEventListener('mouseup', handleGlobalUp);
    window.addEventListener('touchmove', handleGlobalTouchMove, { passive: false });
    window.addEventListener('touchend', handleGlobalUp);
    return () => {
      window.removeEventListener('mousemove', handleGlobalMove);
      window.removeEventListener('mouseup', handleGlobalUp);
      window.removeEventListener('touchmove', handleGlobalTouchMove);
      window.removeEventListener('touchend', handleGlobalUp);
    };
  }, [handleGlobalMove, handleGlobalUp]);

  const handleGlobalTouchMove = (e) => {
     if(activePointIndex !== null || draggingLineId !== null || isGeneralDragging) {
         e.preventDefault(); handleGlobalMove(e);
     }
  };

  const performWarpAndProceed = useCallback(async () => {
    if (!originalImage || !originalImage.src) return; 
    setLoadingText("正在進行透視校正 (Homography)...");
    setIsProcessing(true);
    try {
        const srcW = originalCardDims.w;
        const srcH = originalCardDims.h;

        // 計算裁切區域在原圖中的實際像素尺寸
        const P0 = cropPoints[0], P1 = cropPoints[1], P2 = cropPoints[2], P3 = cropPoints[3];
        const distPx = (pA, pB) => Math.sqrt(Math.pow((pA.x - pB.x) * srcW, 2) + Math.pow((pA.y - pB.y) * srcH, 2));
        
        const avgSrcW = (distPx(P0, P1) + distPx(P3, P2)) / 2;
        const avgSrcH = (distPx(P0, P3) + distPx(P1, P2)) / 2;
        
        if (avgSrcH < 1 || avgSrcW < 1) throw new Error("裁剪區域無效。");
        
        // *** 關鍵修改：動態解析度 ***
        // 目標寬度 = 原圖裁切寬度 (但限制在 MIN ~ MAX 之間)
        // 這樣如果是大圖，就會保持大圖的解析度
        const targetW = Math.max(MIN_TARGET_WIDTH, Math.min(MAX_TARGET_WIDTH, Math.round(avgSrcW)));
        
        // 根據來源比例計算對應的高度
        const ratio = avgSrcW / avgSrcH;
        const targetH = Math.round(targetW / ratio);
        
        const srcPoints = cropPoints.map(p => ([p.x * srcW, p.y * srcH]));
        const dstPoints = [[0, 0], [targetW, 0], [targetW, targetH], [0, targetH]];

        const A = [], B = [];
        for (let i = 0; i < 4; i++) {
            const [x, y] = srcPoints[i], [u, v] = dstPoints[i];
            A.push([x, y, 1, 0, 0, 0, -u * x, -u * y]); B.push(u); 
            A.push([0, 0, 0, x, y, 1, -v * x, -v * y]); B.push(v);
        }
        const solution = Matrix.solveLinearSystem(A, B);
        const H_inv = Matrix.inverse3x3(
            [ (solution.slice(0,3)), (solution.slice(3,6)), (solution.slice(6,8).concat([1])) ].flat().reduce((acc, val, i) => {
                if(i % 3 === 0) acc.push([]);
                acc[acc.length-1].push(val);
                return acc;
            }, [])
        );

        if (!H_inv) throw new Error("矩陣奇異");

        const canvas = document.createElement('canvas');
        canvas.width = targetW; canvas.height = targetH;
        const ctx = canvas.getContext('2d');
        const tempImageForCanvas = await loadImage(originalImage.src);
        const tempCanvas = document.createElement('canvas');
        tempCanvas.width = srcW; tempCanvas.height = srcH;
        const tempCtx = tempCanvas.getContext('2d');
        tempCtx.drawImage(tempImageForCanvas, 0, 0, srcW, srcH);
        
        const srcImageData = tempCtx.getImageData(0, 0, srcW, srcH);
        const dstImageData = ctx.createImageData(targetW, targetH);
        const dstData = dstImageData.data;

        for (let y = 0; y < targetH; y++) {
            for (let x = 0; x < targetW; x++) {
                const target_vector = [[x], [y], [1]];
                const source_homogenous = Matrix.multiply(H_inv, target_vector);
                const wW = source_homogenous[2][0]; 
                const sourceX = source_homogenous[0][0] / wW;
                const sourceY = source_homogenous[1][0] / wW;
                const dstIdx = (y * targetW + x) * 4;
                
                if (sourceX >= 0 && sourceX < srcW - 1 && sourceY >= 0 && sourceY < srcH - 1) {
                    const [r, g, b, a] = bilinearInterpolation(srcImageData, sourceX, sourceY);
                    dstData[dstIdx] = r; dstData[dstIdx + 1] = g; dstData[dstIdx + 2] = b; dstData[dstIdx + 3] = a;
                } else {
                    dstData[dstIdx] = 0; dstData[dstIdx + 1] = 0; dstData[dstIdx + 2] = 0; dstData[dstIdx + 3] = 255;
                }
            }
        }
        
        ctx.putImageData(dstImageData, 0, 0);
        const newImg = new Image();
        newImg.onload = () => {
            setProcessedImage(newImg); setIsProcessing(false); setStep('measure');
            setSelectedLineId(null); setLastInteractionCoords({});
            if (containerRef.current) containerRef.current.scrollTop = 0;
        };
        newImg.src = canvas.toDataURL('image/png'); 
    } catch (error) {
        console.error("Homography error:", error);
        setIsProcessing(false);
    }
  }, [originalImage, originalCardDims, cropPoints]); 

  const calculateResults = () => {
    const topBorder = Math.abs(measureLines.innerTop - measureLines.outerTop);
    const bottomBorder = Math.abs(measureLines.outerBottom - measureLines.innerBottom);
    const leftBorder = Math.abs(measureLines.innerLeft - measureLines.outerLeft);
    const rightBorder = Math.abs(measureLines.outerRight - measureLines.innerRight);
    const totalV = topBorder + bottomBorder || 1;
    const totalH = leftBorder + rightBorder || 1;
    return {
        v: { top: (topBorder / totalV) * 100, bottom: (bottomBorder / totalV) * 100 },
        h: { left: (leftBorder / totalH) * 100, right: (rightBorder / totalH) * 100 }
    };
  };
  const results = calculateResults();

  const nudgeLine = (val) => {
    if (!selectedLineId || !processedImage) return;
    const lineIdToNudge = selectedLineId;
    const imgRect = getLiveImageRect(); 
    if(!imgRect) return;

    const isHLine = lineIdToNudge.includes('Top') || lineIdToNudge.includes('Bottom');
    const pixelSize = isHLine ? imgRect.height : imgRect.width; 
    const pxPct = (1 / pixelSize) * 100;
    
    // *** 關鍵修復：先計算新值，再更新狀態與放大鏡位置 ***
    const currentVal = measureLines[lineIdToNudge];
    const newVal = Math.max(0, Math.min(100, currentVal + (val * pxPct)));
    
    setMeasureLines(prev => ({
        ...prev,
        [lineIdToNudge]: newVal
    }));
    
    // 直接使用新值計算放大鏡位置，確保同步
    // *** 修正: 使用 lastInteractionCoords 來決定「非移動軸」的位置，避免跳回中心 ***
    let targetX, targetY;
    const lastCoords = lastInteractionCoords[lineIdToNudge];

    if (isHLine) {
        // 水平線：保留上一次的 X 座標（或中心），更新 Y 座標
        const lastScreenX = lastCoords ? lastCoords.x : (imgRect.left + imgRect.width / 2);
        targetX = Math.max(imgRect.left, Math.min(imgRect.right, lastScreenX)); // 確保 X 不會飛出圖片外
        targetY = imgRect.top + imgRect.height * (newVal / 100);
    } else {
        // 垂直線：保留上一次的 Y 座標（或中心），更新 X 座標
        const lastScreenY = lastCoords ? lastCoords.y : (imgRect.top + imgRect.height / 2);
        targetX = imgRect.left + imgRect.width * (newVal / 100);
        targetY = Math.max(imgRect.top, Math.min(imgRect.bottom, lastScreenY)); // 確保 Y 不會飛出圖片外
    }
    
    // 更新 lastInteractionCoords，這樣連續點擊時位置不會跑掉
    setLastInteractionCoords(prev => ({
        ...prev,
        [lineIdToNudge]: { x: targetX, y: targetY }
    }));
    
    showFixedMagnifierAt(targetX, targetY); 
  };
  
  // 新增: 微調裁切點 (Crop Points)
  const nudgeCropPoint = (dx, dy) => {
      if (lastActivePointIndex === null || !imgRef.current) return;
      const rect = imgRef.current.getBoundingClientRect();
      if (!rect || rect.width === 0) return;

      // 將像素移動量轉換為 0-1 的比例
      const normDx = dx / rect.width;
      const normDy = dy / rect.height;

      setCropPoints(prev => {
          const newPoints = [...prev];
          const pt = newPoints[lastActivePointIndex];
          newPoints[lastActivePointIndex] = {
              x: Math.max(0, Math.min(1, pt.x + normDx)),
              y: Math.max(0, Math.min(1, pt.y + normDy))
          };
          return newPoints;
      });

      // 手動計算更新後的螢幕位置以顯示放大鏡
      const currentPt = cropPoints[lastActivePointIndex];
      // 注意: 這裡我們預測更新後的位置，因為 setState 是非同步的
      const targetX = rect.left + (currentPt.x + normDx) * rect.width;
      const targetY = rect.top + (currentPt.y + normDy) * rect.height;
      showFixedMagnifierAt(targetX, targetY);
  };
  
  const handleZoomChange = (newZoom) => {
      setZoomLevel(newZoom);
      let targetX, targetY;
      if (step === 'measure' && selectedLineId) {
          const screenCenter = getLineScreenCenter(selectedLineId);
          if (screenCenter) { targetX = screenCenter.x; targetY = screenCenter.y; }
      } else {
          const imgRect = getLiveImageRect();
          if (imgRect) { targetX = imgRect.left + imgRect.width / 2; targetY = imgRect.top + imgRect.height / 2; }
      }
      if (targetX !== undefined) showFixedMagnifierAt(targetX, targetY);
  }

  // New helper: cycle through zoom options
  const cycleZoom = () => {
      const currentIndex = zoomOptions.indexOf(zoomLevel);
      const nextIndex = (currentIndex + 1) % zoomOptions.length;
      handleZoomChange(zoomOptions[nextIndex]);
  };
  
  // 新增: 下載合成結果圖片
  const downloadResultImage = async () => {
    if (!processedImage) return;
    
    const canvas = document.createElement('canvas');
    const ctx = canvas.getContext('2d');
    const w = processedImage.naturalWidth;
    const h = processedImage.naturalHeight;
    
    // 增加底部空間來顯示數據
    const footerHeight = 120;
    canvas.width = w;
    canvas.height = h + footerHeight;
    
    // 填充深色背景
    ctx.fillStyle = '#111827'; 
    ctx.fillRect(0, 0, w, canvas.height);
    
    // 繪製原圖
    ctx.drawImage(processedImage, 0, 0);
    
    // 繪製測量線
    const drawLine = (pct, isH, color) => {
        ctx.strokeStyle = color;
        ctx.lineWidth = 3; 
        ctx.setLineDash([10, 10]);
        ctx.beginPath();
        if (isH) {
            const y = (pct / 100) * h;
            ctx.moveTo(0, y); ctx.lineTo(w, y);
        } else {
            const x = (pct / 100) * w;
            ctx.moveTo(x, 0); ctx.lineTo(x, h);
        }
        ctx.stroke();
    };
    
    const ml = measureLines;
    drawLine(ml.outerTop, true, '#3b82f6');
    drawLine(ml.outerBottom, true, '#3b82f6');
    drawLine(ml.outerLeft, false, '#3b82f6');
    drawLine(ml.outerRight, false, '#3b82f6');
    drawLine(ml.innerTop, true, '#ef4444');
    drawLine(ml.innerBottom, true, '#ef4444');
    drawLine(ml.innerLeft, false, '#ef4444');
    drawLine(ml.innerRight, false, '#ef4444');
    
    // 繪製底部文字
    ctx.setLineDash([]);
    ctx.fillStyle = '#ffffff';
    ctx.font = 'bold 32px sans-serif'; // 這裡假設圖片解析度夠大，如果圖片很小字可能會太大，但一般卡牌掃圖都很大
    ctx.textAlign = 'center';
    
    const res = calculateResults();
    const textV = `上下比例 (V): ${res.v.top.toFixed(1)} : ${res.v.bottom.toFixed(1)}`;
    const textH = `左右比例 (H): ${res.h.left.toFixed(1)} : ${res.h.right.toFixed(1)}`;
    
    // 左右兩邊顯示數據
    ctx.fillText(textH, w * 0.25, h + 70);
    ctx.fillText(textV, w * 0.75, h + 70);
    
    // 中間分隔線
    ctx.strokeStyle = '#374151';
    ctx.lineWidth = 2;
    ctx.beginPath();
    ctx.moveTo(w/2, h + 20);
    ctx.lineTo(w/2, h + 100);
    ctx.stroke();

    // 觸發下載
    const link = document.createElement('a');
    // 修改這裡：使用與 JSON 相同的命名邏輯
    const baseName = originalFileName.replace(/\.[^/.]+$/, "");
    link.download = `${baseName}_grading.png`;
    link.href = canvas.toDataURL('image/png');
    link.click();
  };

  // Define renderDraggableLine INSIDE the component
  const renderDraggableLine = (id, orientation, colorClass, isInner) => {
    const val = measureLines[id];
    const isActive = selectedLineId === id; 
    const isHorizontal = orientation === 'horizontal';
    const style = isHorizontal ? { top: `${val}%` } : { left: `${val}%` };
    const cursor = isHorizontal ? 'cursor-row-resize' : 'cursor-col-resize';
    const hitAreaStyle = isHorizontal ? { top: '-10px', bottom: '-10px', left: 0, right: 0 } : { left: '-10px', right: '-10px', top: 0, bottom: 0 };
    const lineClasses = `absolute w-full h-full border border-dashed transition-colors ${isHorizontal ? 'border-t' : 'border-l'}`;

    return (
        <div key={id} className={`absolute z-20 group ${cursor}`} style={{...style, ...(isHorizontal ? {left:0, right:0, height:0} : {top:0, bottom:0, width:0})}}
            onMouseDown={(e) => handleLineDragStart(id, e)} onTouchStart={(e) => handleLineDragStart(id, e)}>
            <div className={`${lineClasses} ${isActive ? 'border-yellow-400 z-50 shadow-[0_0_5px_rgba(255,255,0,0.8)]' : colorClass}`}></div>
            <div className="absolute bg-transparent" style={hitAreaStyle}></div>
            {isActive && <div className={`absolute ${isHorizontal ? 'left-1/2 -top-6 transform -translate-x-1/2' : 'top-1/2 -left-6 transform -translate-y-1/2'} bg-gray-900 text-[10px] text-white px-1 rounded whitespace-nowrap pointer-events-none`}>{isInner ? '紅線 (圖案)' : '藍線 (卡邊)'}</div>}
        </div>
    );
  };
  
  const [coordsKey, setCoordsKey] = useState(0);
  useEffect(() => { setTimeout(() => setCoordsKey(k => k + 1), 50); }, [step]); 
  const handleBackToCrop = () => { setStep('crop'); setSelectedLineId(null); setProcessedImage(null); };
  
  const isImageStep = step === 'crop' || step === 'measure';
  // 修改：一律使用 items-start，避免強制置中導致手機版頂部被遮擋
  const mainClass = `flex-1 relative w-full overflow-auto select-none p-2 md:p-6 flex justify-center items-start`; 

  return (
    <div className="h-screen bg-gray-950 text-white font-sans flex flex-col overflow-hidden">
      <header className="bg-gray-900 border-b border-gray-800 h-12 flex items-center justify-between px-4 shrink-0 z-50">
        <div className="flex items-center gap-2"><Ruler className="text-blue-400" size={18} /><span className="font-bold text-sm md:text-base bg-gradient-to-r from-blue-400 to-purple-400 bg-clip-text text-transparent">PTCG Grade (虛線修復版 v22)</span></div>
        <div className="flex items-center gap-2 text-xs">{step !== 'upload' && (<button onClick={handleReset} className="hover:text-white text-gray-400 flex items-center gap-1"><RefreshCw size={12}/> 重置</button>)}</div>
      </header>
      <main className={mainClass}>
        {step === 'upload' && (
             // 修改：在手機版增加 pt-12 並使用 justify-start，確保不被 Header 遮擋；電腦版則恢復置中
             <div className="flex-1 flex flex-col items-center justify-start pt-12 md:justify-center md:pt-0 w-full max-w-4xl gap-6 p-6">
                 
                 {/* 狀態提示：如果已載入 JSON */}
                 {pendingProjectData && (
                     <div className="bg-green-900/20 border border-green-500/30 p-3 rounded-lg text-center w-full max-w-sm animate-in fade-in slide-in-from-bottom-4">
                         <div className="flex items-center justify-center gap-2 text-green-400 font-bold text-sm mb-1">
                             <FileJson size={16}/>
                             <span>專案設定已就緒</span>
                         </div>
                         <div className="text-gray-400 text-xs break-all">{pendingProjectData.imageName}</div>
                     </div>
                 )}

                 {/* 主上傳區塊 */}
                 <div className={`w-full max-w-md aspect-[3/4] border-2 border-dashed rounded-2xl transition-all relative flex flex-col items-center justify-center group cursor-pointer shadow-2xl p-6 ${pendingProjectData ? 'border-green-500/50 bg-green-900/10 hover:bg-green-900/20' : 'border-gray-700 bg-gray-900 hover:border-blue-500'}`}>
                     {pendingProjectData ? (
                        <FileImage size={64} className="text-green-500/80 mb-6 animate-pulse" />
                     ) : (
                        <Upload size={64} className="text-gray-600 group-hover:text-blue-400 mb-6 transition-colors"/>
                     )}
                     
                     <input type="file" accept="image/*,.heic,.heif" onChange={handleImageUpload} className="absolute inset-0 opacity-0 cursor-pointer z-10" />
                     
                     <p className={`font-bold text-xl mb-2 ${pendingProjectData ? 'text-green-400' : 'text-gray-300'}`}>
                         {pendingProjectData ? '請上傳對應圖片' : '上傳卡牌照片'}
                     </p>
                     <p className="text-gray-500 text-sm text-center">
                         {pendingProjectData ? '還原校正與測量數據' : '支援 JPG, PNG, HEIC (確保四角清晰)'}
                     </p>
                 </div>

                 {/* 底部按鈕區 */}
                 <div className="flex flex-col items-center gap-3">
                     {!pendingProjectData ? (
                         <div className="relative group">
                             <button className="flex items-center gap-2 text-gray-400 group-hover:text-white px-5 py-2.5 rounded-full border border-gray-700 group-hover:border-gray-500 bg-gray-800/50 transition-all text-sm">
                                 <FileJson size={16} />
                                 <span>載入專案設定 (.json)</span>
                             </button>
                             <input type="file" accept=".json" onChange={handleJsonUpload} className="absolute inset-0 opacity-0 cursor-pointer" />
                         </div>
                     ) : (
                         <button onClick={() => setPendingProjectData(null)} className="text-gray-600 hover:text-gray-400 text-xs py-2 transition-colors">
                             取消載入 (返回一般上傳)
                         </button>
                     )}
                 </div>
             </div>
        )}
        {(step === 'crop' || step === 'measure') && (
            <div className={`flex-shrink-0 select-none ${step === 'measure' ? 'max-h-[85vh] overflow-y-auto bg-gray-800 rounded-xl p-2 w-fit max-w-full' : 'relative w-fit h-fit'}`} ref={containerRef}>
                <div className="relative w-fit h-fit">
                    {/* *** 關鍵修復：補回 BASE_TARGET_WIDTH 的定義後，這裡就不會出錯了 *** */}
                    <img ref={imgRef} src={step === 'crop' ? originalImage?.src : processedImage?.src} alt="Work" className="object-contain pointer-events-none shadow-2xl" style={step === 'crop' ? { maxWidth: `${BASE_TARGET_WIDTH}px`, maxHeight: '80vh' } : (processedImage ? { width: `${processedImage.naturalWidth}px`, height: 'auto' } : {})} />
                    
                    {/* 改良後的放大鏡面板: 可收折 */}
                    {(step === 'crop' || step === 'measure') && (
                        <div className={`fixed right-2 top-1/2 transform -translate-y-1/2 bg-gray-800/90 backdrop-blur-sm rounded-lg shadow-xl z-50 flex flex-col gap-2 border border-gray-700 transition-all duration-300 ${isMagnifierPanelCollapsed ? 'p-2 w-10' : 'p-3'}`}>
                             <button 
                                onClick={() => setIsMagnifierPanelCollapsed(!isMagnifierPanelCollapsed)}
                                className="self-end text-gray-400 hover:text-white mb-1 focus:outline-none"
                                title={isMagnifierPanelCollapsed ? "展開" : "收起"}
                            >
                                {isMagnifierPanelCollapsed ? <ChevronLeft size={16}/> : <ChevronRight size={16}/>}
                            </button>
                            
                            {!isMagnifierPanelCollapsed && (
                                <>
                                    <p className="text-xs text-gray-300 font-semibold mb-1 text-center whitespace-nowrap">放大鏡</p>
                                    {zoomOptions.map(z => (<button key={z} onClick={() => handleZoomChange(z)} className={`w-10 h-10 text-xs font-bold rounded-lg transition-all border ${zoomLevel === z ? 'bg-blue-600 text-white shadow-md border-blue-400' : 'bg-gray-700 text-gray-300 hover:bg-gray-600 border-gray-600'}`}>{z.toFixed(1)}X</button>))}
                                    <p className="text-xs text-gray-500 text-center mt-1">1.0X 原圖</p>
                                </>
                            )}
                            {isMagnifierPanelCollapsed && (
                                <div className="flex flex-col items-center gap-1">
                                    <button 
                                        onClick={cycleZoom}
                                        className="text-[10px] font-bold text-blue-400 hover:text-white transition-colors w-full text-center"
                                        title="點擊切換倍率"
                                    >
                                        {zoomLevel.toFixed(1)}X
                                    </button>
                                </div>
                            )}
                        </div>
                    )}
                    
                    {step === 'crop' && originalImage && (
                        <CropOverlay 
                            cropPoints={cropPoints} 
                            getImageContainerRect={getLiveImageRect} 
                            getScreenCoords={getScreenCoords} 
                            activePointIndex={activePointIndex}
                            lastActivePointIndex={lastActivePointIndex} // 傳入最後操作的點
                            handleCropDragStart={handleCropDragStart} 
                            imgRef={imgRef} 
                            key={`crop-overlay-${coordsKey}`} 
                        />
                    )}
                    {step === 'measure' && processedImage && (
                        // *** 新增事件監聽：在圖片容器上監聽 MouseDown 和 TouchStart，觸發一般放大鏡檢查 ***
                        <div 
                            className="absolute inset-0 w-full h-full pointer-events-auto cursor-crosshair"
                            onMouseDown={handleGeneralDragStart}
                            onTouchStart={handleGeneralDragStart}
                        > 
                            {renderDraggableLine('outerTop', 'horizontal', 'border-blue-500', false)}
                            {renderDraggableLine('outerBottom', 'horizontal', 'border-blue-500', false)}
                            {renderDraggableLine('outerLeft', 'vertical', 'border-blue-500', false)}
                            {renderDraggableLine('outerRight', 'vertical', 'border-blue-500', false)}
                            {renderDraggableLine('innerTop', 'horizontal', 'border-red-500', true)}
                            {renderDraggableLine('innerBottom', 'horizontal', 'border-red-500', true)}
                            {renderDraggableLine('innerLeft', 'vertical', 'border-red-500', true)}
                            {renderDraggableLine('innerRight', 'vertical', 'border-red-500', true)}
                        </div>
                    )}
                </div>
                {isProcessing && (<div className="fixed inset-0 bg-black/80 z-50 flex flex-col items-center justify-center text-white"><Loader2 className="animate-spin mb-4" size={40}/><p>{loadingText}</p></div>)}
            </div>
        )}
      </main>
      <Magnifier magnifierState={{...magnifier, cropPoints: cropPoints, measureLines: measureLines, currentStep: step}} zoom={zoomLevel} cardImage={cardImageForMagnifier}/>
      <footer className="bg-gray-900 border-t border-gray-800 p-3 shrink-0 z-40">
        <div className="max-w-4xl mx-auto w-full">
            {step === 'crop' && (
                <div className="flex flex-col md:flex-row items-center justify-between gap-3">
                     <div className="flex flex-col gap-1 w-full md:w-auto">
                        <div className="text-gray-400 text-xs md:text-sm"><span className="text-green-400 font-bold">步驟 1:</span> 拖曳四個綠點至卡牌角落</div>
                        <div className="text-gray-500 text-[10px]">點擊任一綠點即可進行微調</div>
                     </div>
                     
                     {/* 新增: 校正微調控制器 */}
                     <div className="flex items-center gap-2 bg-gray-800/50 p-1.5 rounded-lg border border-gray-700">
                         <div className="flex flex-col items-center justify-center gap-1">
                             <button onClick={() => nudgeCropPoint(0, -1)} disabled={lastActivePointIndex === null} className={`w-8 h-8 rounded bg-gray-700 flex items-center justify-center ${lastActivePointIndex !== null ? 'hover:bg-blue-600 text-white' : 'opacity-30 cursor-not-allowed'}`}><ChevronUp size={16}/></button>
                             <div className="flex gap-1">
                                 <button onClick={() => nudgeCropPoint(-1, 0)} disabled={lastActivePointIndex === null} className={`w-8 h-8 rounded bg-gray-700 flex items-center justify-center ${lastActivePointIndex !== null ? 'hover:bg-blue-600 text-white' : 'opacity-30 cursor-not-allowed'}`}><ChevronLeft size={16}/></button>
                                 <div className="w-8 h-8 flex items-center justify-center text-blue-400">
                                     {lastActivePointIndex !== null ? <Move size={16} /> : <MousePointerClick size={16} className="text-gray-600"/>}
                                 </div>
                                 <button onClick={() => nudgeCropPoint(1, 0)} disabled={lastActivePointIndex === null} className={`w-8 h-8 rounded bg-gray-700 flex items-center justify-center ${lastActivePointIndex !== null ? 'hover:bg-blue-600 text-white' : 'opacity-30 cursor-not-allowed'}`}><ChevronRight size={16}/></button>
                             </div>
                             <button onClick={() => nudgeCropPoint(0, 1)} disabled={lastActivePointIndex === null} className={`w-8 h-8 rounded bg-gray-700 flex items-center justify-center ${lastActivePointIndex !== null ? 'hover:bg-blue-600 text-white' : 'opacity-30 cursor-not-allowed'}`}><ChevronDown size={16}/></button>
                         </div>
                         <div className="text-[10px] text-gray-500 w-16 text-center leading-tight">
                             {lastActivePointIndex !== null ? '微調選中點' : '請先點選綠點'}
                         </div>
                     </div>

                     <button onClick={performWarpAndProceed} className="bg-green-600 hover:bg-green-500 text-white px-6 py-2 rounded-full font-bold shadow-lg flex items-center gap-2 active:scale-95 transition-all w-full md:w-auto justify-center">校正並繼續 <ArrowRight size={18}/></button>
                </div>
            )}
            {step === 'measure' && (
                <div className="flex flex-col gap-3">
                    <div className="flex items-center justify-between"><button onClick={handleBackToCrop} className="text-gray-500 hover:text-white px-2 py-1 flex items-center gap-1 text-xs"><ArrowLeft size={14}/> 重調四角 (保留上次位置)</button><div className="flex items-center gap-2"><button onClick={() => nudgeLine(-1)} disabled={!selectedLineId} className={`w-10 h-10 rounded-full flex items-center justify-center border transition-colors ${selectedLineId ? 'bg-gray-800 hover:bg-gray-700 border-gray-700 text-white' : 'bg-gray-900 border-gray-800 text-gray-600 cursor-not-allowed'}`}>{(selectedLineId?.includes('Top') || selectedLineId?.includes('Bottom')) ? <ChevronUp size={20}/> : <ChevronLeft size={20}/>}</button><div className="text-center w-24"><div className="text-[10px] text-gray-500 uppercase tracking-wider">微調</div><div className="text-xs font-bold text-blue-300 truncate">{selectedLineId ? (selectedLineId.includes('outer') ? '藍線 (卡邊)' : '紅線 (圖案)') : '請點選虛線'}</div></div><button onClick={() => nudgeLine(1)} disabled={!selectedLineId} className={`w-10 h-10 rounded-full flex items-center justify-center border transition-colors ${selectedLineId ? 'bg-gray-800 hover:bg-gray-700 border-gray-700 text-white' : 'bg-gray-900 border-gray-800 text-gray-600 cursor-not-allowed'}`}>{(selectedLineId?.includes('Top') || selectedLineId?.includes('Bottom')) ? <ChevronDown size={20}/> : <ChevronRight size={20}/>}</button></div><div className="flex justify-end gap-2"><button onClick={handleExportJSON} className="bg-blue-600 hover:bg-blue-500 text-white p-2 rounded-lg shadow-sm transition-colors" title="儲存專案檔 (.json)"><FileJson size={20}/></button><button onClick={downloadResultImage} className="bg-emerald-600 hover:bg-emerald-500 text-white p-2 rounded-lg shadow-sm transition-colors" title="下載結果圖 (.png)"><ImageIcon size={20}/></button></div></div>
                    <div className="bg-black/40 rounded-lg p-2 flex items-center justify-around border border-gray-700"><div className="flex flex-col items-center w-1/2 border-r border-gray-700"><span className="text-[10px] text-gray-400 uppercase">左右比例 (H)</span><div className="flex items-baseline gap-1"><span className={`text-lg font-bold ${Math.abs(results.h.left - results.h.right) <= 10 ? 'text-green-400' : 'text-yellow-400'}`}>{results.h.left.toFixed(1)} : {results.h.right.toFixed(1)}</span></div></div><div className="flex flex-col items-center w-1/2"><span className="text-[10px] text-gray-400 uppercase">上下比例 (V)</span><div className="flex items-baseline gap-1"><span className={`text-lg font-bold ${Math.abs(results.v.top - results.v.bottom) <= 10 ? 'text-green-400' : 'text-yellow-400'}`}>{results.v.top.toFixed(1)} : {results.v.bottom.toFixed(1)}</span></div></div></div>
                </div>
            )}
        </div>
      </footer>
    </div>
  );
}

const CropOverlay = ({ cropPoints, renderedImageRect, getScreenCoords, activePointIndex, lastActivePointIndex, handleCropDragStart, imgRef, getImageContainerRect }) => {
    // 確保這裡使用正確的 rect 獲取方式
    const containerRect = getImageContainerRect ? getImageContainerRect() : (imgRef.current?.getBoundingClientRect() || renderedImageRect);
    
    if (!containerRect || containerRect.width === 0) return null;
    
    // 計算螢幕座標 (僅用於 SVG 多邊形，因為 SVG 需要絕對像素值)
    const screenPoints = cropPoints.map(p => { 
        const c = getScreenCoords(p.x, p.y); 
        return { c, p, originalIndex: cropPoints.indexOf(p) }; 
    });
    
    if (screenPoints.length !== 4) return null; 
    
    // SVG 點位 (使用像素座標)
    const polygonPoints = screenPoints.map(item => `${item.c.x - containerRect.left},${item.c.y - containerRect.top}`).join(' ');

    return (
        <>
            <svg className="absolute inset-0 w-full h-full pointer-events-none">
                <polygon points={polygonPoints} fill="rgba(34, 197, 94, 0.1)" stroke="rgba(34, 197, 94, 0.8)" strokeWidth="2" strokeDasharray="5" />
            </svg>
            {screenPoints.map((item, i) => {
                const isActive = activePointIndex === item.originalIndex;
                const isSelected = lastActivePointIndex === item.originalIndex;
                
                // *** 關鍵修復 ***
                // 這裡改用 percentage (%) 定位，並且設為 absolute
                // 這樣拖動點就會相對於圖片容器定位，滾動時會緊貼圖片
                const leftPct = `${item.p.x * 100}%`;
                const topPct = `${item.p.y * 100}%`;

                return (
                    <div 
                        key={item.originalIndex} 
                        className={`absolute w-8 h-8 -ml-4 -mt-4 rounded-full border-2 cursor-move flex items-center justify-center shadow-[0_0_10px_rgba(0,0,0,0.5)] pointer-events-auto transition-transform ${isActive ? 'bg-green-400 border-white scale-125 z-30' : (isSelected ? 'bg-green-500 border-yellow-400 z-25 scale-110 shadow-[0_0_10px_rgba(250,204,21,0.6)]' : 'bg-green-500/80 border-green-200 z-20')}`} 
                        style={{ left: leftPct, top: topPct }} 
                        onMouseDown={(e) => handleCropDragStart(item.originalIndex, e)} 
                        onTouchStart={(e) => handleCropDragStart(item.originalIndex, e)}
                    >
                        <Move size={14} className={isSelected ? "text-yellow-100" : "text-black"} />
                    </div>
                );
            })}
        </>
    );
};

export default function App() {
    return (
        <CardGraderTool />
    )
}